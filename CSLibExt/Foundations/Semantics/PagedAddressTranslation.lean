/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Logic.Function.Basic

/-!
# Paged address translation

A model of one address space with natural-number byte addresses and `2 ^ bits` bytes per page.
The page table is a function on abstract slot addresses, and the translation cache is a partial
map from virtual page numbers to frames and permissions. Use each cache with the same table and
page size throughout. The model has no memory effects, address-width limits, or cache eviction.

`translate_spec` gives the address split and the exact result and cache state in terms of a table
walk, assuming every cached mapping agrees with a valid, present entry in the table.

## References

R. H. Arpaci-Dusseau and A. C. Arpaci-Dusseau, *Operating Systems: Three Easy Pieces*, v1.10,
Chapters 18–19, especially Figures 18.6 and 19.1. We check presence after validity and permission,
combining the figures with the discussion of the present bit in §18.3. A successful miss fills
the cache and returns the translated address in one step rather than retrying an instruction.
-/

@[expose] public section

namespace Cslib.Semantics.PagedAddressTranslation

/-- Kinds of access distinguished by the permission check. -/
inductive Access where
  | read
  | write
  | execute

/-- Reasons for an unsuccessful translation: invalid page, denied access, or nonresident page. -/
inductive Fault where
  | invalid
  | protection
  | nonresident

/-- The physical frame number and permissions of a virtual page. -/
structure Mapping where
  /-- The physical frame number. -/
  frame : Nat
  /-- Whether each kind of access is permitted. -/
  allows : Access → Bool

/-- A table entry also records whether the page is in use and resident. -/
structure PageTableEntry where
  /-- Whether the page is in use. -/
  valid : Bool
  /-- Whether the page is resident. -/
  present : Bool
  /-- The frame and permissions fields. -/
  mapping : Mapping

/-- An abstract linear page table for one address space. Unused pages have invalid entries. -/
structure PageTable where
  /-- The starting byte address of the table. -/
  base : Nat
  /-- The size in bytes of one entry. -/
  entryBytes : Nat
  /-- Entries have positive size. -/
  entryBytes_pos : 0 < entryBytes
  /-- Abstract entry contents at slot addresses; no physical memory is accessed. -/
  entryAt : Nat → PageTableEntry

/-- With `bits` offset bits, a page or frame contains `2 ^ bits` bytes. -/
def pageSize (bits : Nat) : Nat := 2 ^ bits

/-- Virtual page number: the quotient after discarding the offset bits. -/
def vpn (bits address : Nat) : Nat := address / pageSize bits

/-- Offset within a page or frame: the remainder after division by the page size. -/
def offset (bits address : Nat) : Nat := address % pageSize bits

/-- A linear table's entry for page `page` starts at `base + page * entryBytes`. -/
def PageTable.entryAddress (table : PageTable) (page : Nat) : Nat :=
  table.base + page * table.entryBytes

/-- Look up a page's entry at its abstract linear-table slot address. -/
def PageTable.lookup (table : PageTable) (page : Nat) : PageTableEntry :=
  table.entryAt (table.entryAddress page)

/-- Check validity, then permission, then residence. A successful walk returns the mapping. -/
def walk (table : PageTable) (access : Access) (page : Nat) : Except Fault Mapping :=
  let entry := table.lookup page
  if !entry.valid then .error .invalid
  else if !(entry.mapping.allows access) then .error .protection
  else if !entry.present then .error .nonresident
  else .ok entry.mapping

/-- One address space's translation cache, indexed by virtual page number. -/
abbrev Cache := Nat → Option Mapping

/-- Every cached mapping agrees with a valid, present entry of the same table. -/
def Cache.AgreesWith (cache : Cache) (table : PageTable) : Prop :=
  ∀ ⦃page mapping⦄, cache page = some mapping →
    let entry := table.lookup page
    entry.valid = true ∧ entry.present = true ∧ entry.mapping = mapping

/-- Resolve one byte address, returning the outcome and the next cache. A hit checks cached
permissions without a walk. Only a successful miss adds a mapping to the cache. -/
def translate (table : PageTable) (cache : Cache) (bits : Nat) (access : Access)
    (address : Nat) : Except Fault Nat × Cache :=
  let page := vpn bits address
  let finish (mapping : Mapping) := mapping.frame * pageSize bits + offset bits address
  match cache page with
  | some mapping =>
    (if mapping.allows access then .ok (finish mapping) else .error .protection, cache)
  | none =>
    match walk table access page with
    | .error fault => (.error fault, cache)
    | .ok mapping => (.ok (finish mapping), Function.update cache page (some mapping))

private theorem walk_ok {table : PageTable} {access : Access} {page : Nat} {mapping : Mapping}
    (h : walk table access page = .ok mapping) :
    (table.lookup page).valid = true ∧ (table.lookup page).present = true ∧
      (table.lookup page).mapping = mapping := by
  cases hv : (table.lookup page).valid <;>
    cases ha : (table.lookup page).mapping.allows access <;>
    cases hp : (table.lookup page).present <;>
    simp_all [walk]

/-- **Paged address translation.** The virtual address splits into a page number and a bounded
byte offset. For a cache that agrees with the table, translation gives the same outcome as a
walk and preserves agreement. On failure the cache is unchanged; on success the address has
the walk's frame number and the original offset, and the cache records that page's mapping
(an update to the same value on a hit). -/
theorem translate_spec (table : PageTable) (cache : Cache) (bits : Nat) (access : Access)
    (address : Nat) (hcache : cache.AgreesWith table) :
    let size := pageSize bits
    let page := vpn bits address
    let off := offset bits address
    let result := translate table cache bits access address
    page * size + off = address ∧ off < size ∧ result.2.AgreesWith table ∧
      match walk table access page with
      | .error fault => result = (.error fault, cache)
      | .ok mapping =>
        result = (.ok (mapping.frame * size + off), Function.update cache page (some mapping)) ∧
          (mapping.frame * size + off) / size = mapping.frame ∧
          (mapping.frame * size + off) % size = off := by
  dsimp only
  have hsize : 0 < pageSize bits := Nat.two_pow_pos bits
  have hoff : offset bits address < pageSize bits := Nat.mod_lt _ hsize
  refine ⟨Nat.div_add_mod' _ _, hoff, ?_⟩
  have hframe (frame : Nat) :
      (frame * pageSize bits + offset bits address) / pageSize bits = frame := by
    rw [Nat.mul_comm frame, Nat.mul_add_div hsize, Nat.div_eq_of_lt hoff, Nat.add_zero]
  have hrem (frame : Nat) : (frame * pageSize bits + offset bits address) % pageSize bits =
      offset bits address :=
    (Nat.mul_add_mod_self_right _ _ _).trans (Nat.mod_eq_of_lt hoff)
  cases hit : cache (vpn bits address) with
  | none =>
    cases walked : walk table access (vpn bits address) with
    | error fault =>
      exact ⟨by simpa only [translate, hit, walked] using hcache, by simp [translate, hit, walked]⟩
    | ok mapping =>
      simp only [translate, hit, walked]
      refine ⟨?_, trivial, hframe _, hrem _⟩
      intro page entry found
      by_cases hpage : page = vpn bits address
      · subst page
        rw [Function.update_self, Option.some.injEq] at found
        subst entry
        exact walk_ok walked
      · exact hcache (by simpa only [Function.update_of_ne hpage] using found)
  | some mapping =>
    obtain ⟨hvalid, hpresent, hmapping⟩ := hcache hit
    cases allowed : mapping.allows access with
    | false =>
      have walked : walk table access (vpn bits address) = .error .protection := by
        simp [walk, hvalid, hmapping, allowed]
      simp [translate, hit, allowed, walked, hcache]
    | true =>
      have walked : walk table access (vpn bits address) = .ok mapping := by
        simp [walk, hvalid, hpresent, hmapping, allowed]
      have hself : Function.update cache (vpn bits address) (some mapping) = cache := by
        rw [← hit, Function.update_eq_self]
      simp [translate, hit, allowed, walked, hcache, hself, hframe, hrem]

end Cslib.Semantics.PagedAddressTranslation
