/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Data.List.Lemmas

/-!
# Bounded-exhaustive checking

A passing bounded check is a proof only relative to the stated bound and the
exact-support hypothesis (`hexact`). It says nothing about elements above the
bound. Plausible/search-based testing is not a universal proof.
-/

@[expose] public section

namespace CSLibExt.Testing.BoundedExhaustive

/--
Bounded-exhaustive iff: under exact support, the bounded `List.all` check
passes exactly when the predicate holds for every element within the bound.
-/
theorem all_iff_forall_le {α : Type _} {enum : Nat → List α} {size : α → Nat}
    (p : α → Bool) (n : Nat) (hexact : ∀ x, x ∈ enum n ↔ size x ≤ n) :
    (enum n).all p = true ↔ ∀ x, size x ≤ n → p x = true := by
  rw [List.all_eq_true]
  constructor
  · intro h x hle
    exact h x ((hexact x).mpr hle)
  · intro h x hx
    exact h x ((hexact x).mp hx)

/--
Passing implies bounded validity under completeness alone. The converse is not
justified under this weaker hypothesis: without soundness, validity need not
imply passing.
-/
theorem forall_le_of_all {α : Type _} {enum : Nat → List α} {size : α → Nat}
    (p : α → Bool) {n : Nat}
    (hcomplete : ∀ x, size x ≤ n → x ∈ enum n)
    (hall : (enum n).all p = true) : ∀ x, size x ≤ n → p x = true := by
  rw [List.all_eq_true] at hall
  intro x hle
  exact hall x (hcomplete x hle)

/--
Support monotonicity derived from exact support (not assumed separately):
membership at a smaller bound implies membership at any larger bound.
-/
theorem mem_of_mem_le {α : Type _} {enum : Nat → List α} {size : α → Nat}
    {m n : Nat} {x : α} (hexact : ∀ n x, x ∈ enum n ↔ size x ≤ n)
    (hle : m ≤ n) (hx : x ∈ enum m) : x ∈ enum n := by
  have h1 : size x ≤ m := (hexact m x).mp hx
  have h2 : size x ≤ n := Nat.le_trans h1 hle
  exact (hexact n x).mpr h2

/--
Product enumeration by remaining budget: enumerate the first component once
at the full bound, and pair each element `a` with every element of `enumB`
within the remaining budget `n - sizeA a`. Each pair is generated at exactly
one first component (up to duplicates inside the input enumerators
themselves). This is not the naive `enumA n × enumB n` form.
-/
def enumProd {α β : Type _} (sizeA : α → Nat) (enumA : Nat → List α)
    (enumB : Nat → List β) (n : Nat) : List (α × β) :=
  (enumA n).flatMap fun a => (enumB (n - sizeA a)).map (fun b => (a, b))

/--
Membership in the budget-split product holds exactly for pairs whose sizes
sum to at most the bound.
-/
theorem mem_enumProd_iff {α β : Type _} {enumA : Nat → List α}
    {enumB : Nat → List β} {sizeA : α → Nat} {sizeB : β → Nat} {a : α} {b : β}
    {n : Nat} (hexactA : ∀ n a, a ∈ enumA n ↔ sizeA a ≤ n)
    (hexactB : ∀ n b, b ∈ enumB n ↔ sizeB b ≤ n) :
    (a, b) ∈ enumProd sizeA enumA enumB n ↔ sizeA a + sizeB b ≤ n := by
  unfold enumProd
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨a', ha', hmem⟩
    rw [List.mem_map] at hmem
    obtain ⟨b', hb', hpair⟩ := hmem
    rw [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    have ha : sizeA a' ≤ n := (hexactA n a').mp ha'
    have hb : sizeB b' ≤ n - sizeA a' := (hexactB _ b').mp hb'
    omega
  · intro hle
    refine ⟨a, (hexactA n a).mpr (by omega), ?_⟩
    rw [List.mem_map]
    exact ⟨b, (hexactB _ b).mpr (by omega), rfl⟩

end CSLibExt.Testing.BoundedExhaustive
