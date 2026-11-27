/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Data.List.Basic
import all Batteries.Data.List.Basic
import Init.Data.Array.Lemmas
import Lean.Elab.Tactic.Omega

/-! # Facts about the canonical Batteries list grouping operation -/

@[expose] public section

set_option autoImplicit false
universe u
namespace List

private theorem flatten_toChunks_go {α : Type u} (n : Nat) (xs : List α)
    (acc : Array α) (groups : Array (List α)) :
    (toChunks.go n xs acc groups).flatten = groups.toList.flatten ++ acc.toList ++ xs := by
  induction xs generalizing acc groups with
  | nil => simp [toChunks.go, Array.toList_push, List.flatten_append]
  | cons x xs ih =>
      rw [toChunks.go]
      split <;> simp [ih, Array.mkEmpty_eq, Array.toList_push, List.flatten_append,
        List.append_assoc]

@[simp] theorem flatten_toChunks {α : Type u} (n : Nat) (xs : List α) :
    (toChunks n xs).flatten = xs := by
  cases xs with
  | nil => simp [toChunks]
  | cons x xs =>
      cases n with
      | zero => simp [toChunks]
      | succ n => simp [toChunks, flatten_toChunks_go]

theorem mem_of_mem_toChunks {α : Type u} {n : Nat} {xs chunk : List α} {x : α}
    (hchunk : chunk ∈ toChunks n xs) (hx : x ∈ chunk) : x ∈ xs := by
  have hflatten : x ∈ (toChunks n xs).flatten :=
    mem_flatten.mpr ⟨chunk, hchunk, hx⟩
  simpa only [flatten_toChunks] using hflatten

private theorem length_le_of_mem_toChunks_go {α : Type u} (n : Nat) (xs : List α)
    (acc : Array α) (groups : Array (List α)) (hn : 0 < n) (ha : acc.size ≤ n)
    (hg : ∀ chunk ∈ groups.toList, chunk.length ≤ n) :
    ∀ chunk ∈ toChunks.go n xs acc groups, chunk.length ≤ n := by
  induction xs generalizing acc groups with
  | nil =>
      intro chunk hchunk
      simp only [toChunks.go, Array.toList_push, mem_append, mem_singleton] at hchunk
      rcases hchunk with hchunk | rfl
      · exact hg chunk hchunk
      · simpa using ha
  | cons x xs ih =>
      rw [toChunks.go]
      split
      · apply ih _ _ (by simpa [Array.mkEmpty_eq] using Nat.succ_le_of_lt hn)
        intro chunk hchunk
        simp only [Array.toList_push, mem_append, mem_singleton] at hchunk
        rcases hchunk with hchunk | rfl
        · exact hg chunk hchunk
        · simpa using ha
      · rename_i h
        apply ih _ _ ?_ hg
        simp only [Array.size_push]
        simp only [beq_iff_eq] at h
        omega

/-- **Chunks of a list have length at most the chunk size.** Let $n > 0$ and let $L$ be a list.
Split $L$ from left to right into consecutive chunks of size $n$: elements go into the current
chunk until it holds $n$ elements, then a new chunk is started. Every chunk produced has at most
$n$ elements. -/
theorem length_le_of_mem_toChunks {α : Type u} (n : Nat) (xs : List α)
    (hn : 0 < n) (chunk : List α) (hchunk : chunk ∈ toChunks n xs) :
    chunk.length ≤ n := by
  cases xs with
  | nil => simp [toChunks] at hchunk
  | cons x xs =>
      cases n with
      | zero => omega
      | succ n =>
          apply length_le_of_mem_toChunks_go (n + 1) xs #[x] #[] hn (by simp) (by simp)
          simpa only [toChunks] using hchunk

/-- Count invariant for the actual `toChunks.go` loop. -/
private theorem length_toChunks_go {α : Type u} (n : Nat) (hn : 0 < n) :
    ∀ (xs : List α) (acc : Array α) (groups : Array (List α)),
      0 < acc.size → acc.size ≤ n →
      (toChunks.go n xs acc groups).length
        = groups.size + 1 + (acc.size + xs.length - 1) / n := by
  intro xs
  induction xs with
  | nil =>
    intro acc groups hpos hle
    rw [toChunks.go, Array.length_toList, Array.size_push]
    have hz : (acc.size + ([] : List α).length - 1) / n = 0 :=
      Nat.div_eq_of_lt (by simp; omega)
    omega
  | cons y ys ih =>
    intro acc groups hpos hle
    rw [toChunks.go]
    simp only [List.length_cons]
    split
    · rename_i h
      have hsize : acc.size = n := by simpa using h
      have hs1 : ((Array.mkEmpty n).push y).size = 1 := by simp
      rw [ih ((Array.mkEmpty n).push y) (groups.push acc.toList)
          (by rw [hs1]; omega) (by rw [hs1]; omega)]
      rw [Array.size_push, hs1]
      have e1 : 1 + ys.length - 1 = ys.length := by omega
      have e2 : acc.size + (ys.length + 1) - 1 = ys.length + n := by omega
      rw [e1, e2, Nat.add_div_right ys.length hn]
      omega
    · rename_i h
      have hne : acc.size ≠ n := by simpa using h
      have hs1 : (acc.push y).size = acc.size + 1 := Array.size_push y
      rw [ih (acc.push y) groups (by rw [hs1]; omega) (by rw [hs1]; omega)]
      rw [hs1]
      have e : acc.size + 1 + ys.length - 1 = acc.size + (ys.length + 1) - 1 := by omega
      rw [e]

theorem length_toChunks {α : Type u} (n : Nat) (xs : List α) (hn : 0 < n) :
    (toChunks n xs).length = (xs.length + n - 1) / n := by
  cases xs with
  | nil =>
    rw [toChunks.eq_1]
    simp only [List.length_nil]
    rw [Nat.div_eq_of_lt (show 0 + n - 1 < n by omega)]
  | cons x xs =>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    show (toChunks.go (k + 1) xs #[x] #[]).length = _
    rw [length_toChunks_go (k + 1) (by omega) xs #[x] #[] (by simp) (by simp)]
    have hx : (#[x] : Array α).size = 1 := by simp
    have he : (#[] : Array (List α)).size = 0 := by simp
    rw [hx, he, List.length_cons]
    have e1 : 1 + xs.length - 1 = xs.length := by omega
    have e2 : xs.length + 1 + (k + 1) - 1 = xs.length + (k + 1) := by omega
    rw [e1, e2, Nat.add_div_right xs.length (by omega)]
    omega

/-- Nonempty invariant for the actual `toChunks.go` loop. -/
private theorem ne_nil_of_mem_toChunks_go {α : Type u} (n : Nat) :
    ∀ (xs : List α) (acc : Array α) (groups : Array (List α)),
      (∀ g ∈ groups, g ≠ []) → 0 < acc.size →
      ∀ c ∈ toChunks.go n xs acc groups, c ≠ [] := by
  intro xs
  induction xs with
  | nil =>
    intro acc groups hg hpos c hc
    rw [toChunks.go, Array.toList_push, List.mem_append] at hc
    rcases hc with hc | hc
    · exact hg c (Array.mem_def.mpr hc)
    · rw [List.mem_singleton] at hc
      subst hc
      intro hcontra
      have : acc.toList.length = 0 := by rw [hcontra]; rfl
      rw [Array.length_toList] at this
      omega
  | cons y ys ih =>
    intro acc groups hg hpos c hc
    rw [toChunks.go] at hc
    split at hc
    · refine ih ((Array.mkEmpty n).push y) (groups.push acc.toList) ?_ (by simp) c hc
      intro g hgmem
      rw [Array.mem_push] at hgmem
      rcases hgmem with hgmem | hgmem
      · exact hg g hgmem
      · subst hgmem
        intro hcontra
        have : acc.toList.length = 0 := by rw [hcontra]; rfl
        rw [Array.length_toList] at this
        omega
    · exact ih (acc.push y) groups hg (by rw [Array.size_push]; omega) c hc

theorem ne_nil_of_mem_toChunks {α : Type u} (n : Nat) (xs : List α)
    (chunk : List α) (hchunk : chunk ∈ toChunks n xs) :
    chunk ≠ [] := by
  cases xs with
  | nil =>
    rw [toChunks.eq_1] at hchunk
    simp at hchunk
  | cons x xs =>
    cases n with
    | zero =>
      rw [show toChunks 0 (x :: xs) = [x :: xs] from rfl, List.mem_singleton] at hchunk
      subst hchunk
      exact List.cons_ne_nil x xs
    | succ k =>
      rw [show toChunks (k + 1) (x :: xs) = toChunks.go (k + 1) xs #[x] #[] from rfl] at hchunk
      exact ne_nil_of_mem_toChunks_go (k + 1) xs #[x] #[] (by intro g hg; simp at hg) (by simp) chunk hchunk

/-- Full-prefix size invariant for the actual `toChunks.go` loop. -/
private theorem length_eq_of_mem_dropLast_toChunks_go {α : Type u} (n : Nat) :
    ∀ (xs : List α) (acc : Array α) (groups : Array (List α)),
      (∀ g ∈ groups, g.length = n) →
      ∀ c ∈ (toChunks.go n xs acc groups).dropLast, c.length = n := by
  intro xs
  induction xs with
  | nil =>
    intro acc groups hg c hc
    rw [toChunks.go, Array.toList_push, List.dropLast_concat] at hc
    exact hg c (Array.mem_def.mpr hc)
  | cons y ys ih =>
    intro acc groups hg c hc
    rw [toChunks.go] at hc
    split at hc
    · rename_i h
      refine ih ((Array.mkEmpty n).push y) (groups.push acc.toList) ?_ c hc
      intro g hgmem
      rw [Array.mem_push] at hgmem
      rcases hgmem with hgmem | hgmem
      · exact hg g hgmem
      · subst hgmem
        rw [Array.length_toList]
        exact (by simpa using h : acc.size = n)
    · exact ih (acc.push y) groups hg c hc

theorem length_eq_of_mem_dropLast_toChunks {α : Type u} (n : Nat) (xs : List α)
    (chunk : List α) (hchunk : chunk ∈ (toChunks n xs).dropLast) :
    chunk.length = n := by
  cases xs with
  | nil =>
    rw [toChunks.eq_1] at hchunk
    simp at hchunk
  | cons x xs =>
    cases n with
    | zero =>
      rw [show toChunks 0 (x :: xs) = [x :: xs] from rfl] at hchunk
      simp at hchunk
    | succ k =>
      rw [show toChunks (k + 1) (x :: xs) = toChunks.go (k + 1) xs #[x] #[] from rfl] at hchunk
      exact length_eq_of_mem_dropLast_toChunks_go (k + 1) xs #[x] #[] (by intro g hg; simp at hg) chunk hchunk


end List
end
