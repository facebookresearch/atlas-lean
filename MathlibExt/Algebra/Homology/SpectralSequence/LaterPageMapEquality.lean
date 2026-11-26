/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
/-!
# Equality of spectral-sequence maps on later pages

For morphisms α,β of spectral sequences with arbitrary page shapes, equality of their maps at
a page N propagates through successor homology to every r≥N. The same equality holds on every
component object, with the starting-page bound retained.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w t

namespace CategoryTheory.SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type t} {c : ℤ → ComplexShape ι} {r₀ : ℤ}
  {S T : SpectralSequence C c r₀}

/-- Equality of page maps passes to the successor page.

Equal maps at r give equal maps at r+1 through spectral successor compatibility. -/
theorem Hom.hom_eq_successor_of_hom_eq (α β : S ⟶ T) (r : ℤ) (hr : r₀ ≤ r)
    (h : α.hom r hr = β.hom r hr) :
    α.hom (r + 1) (by omega) = β.hom (r + 1) (by omega) := by
  apply HomologicalComplex.hom_ext
  intro i
  apply (cancel_epi ((S.iso r (r + 1) i rfl hr).hom)).mp
  calc
    _ = HomologicalComplex.homologyMap (α.hom r hr) i ≫
        (T.iso r (r + 1) i rfl hr).hom := (α.comm r (r + 1) i rfl hr).symm
    _ = HomologicalComplex.homologyMap (β.hom r hr) i ≫
        (T.iso r (r + 1) i rfl hr).hom := by rw [h]
    _ = _ := β.comm r (r + 1) i rfl hr

/-- Equality of page maps persists through finitely many successors.

If α_N=β_N, then α_{N+n}=β_{N+n} for every n∈ℕ. -/
theorem Hom.hom_eq_add_nat_of_hom_eq (α β : S ⟶ T) (N : ℤ) (hN : r₀ ≤ N)
    (h : α.hom N hN = β.hom N hN) (n : ℕ) :
    α.hom (N + (n : ℤ)) (by omega) = β.hom (N + (n : ℤ)) (by omega) := by
  let P : ℤ → Prop := fun r ↦ ∀ hr : r₀ ≤ r, α.hom r hr = β.hom r hr
  have hall : ∀ n : ℕ, P (N + (n : ℤ)) := by
    intro n
    induction n with
    | zero =>
      have hbase : P N := by intro hr; exact h
      exact (congrArg P (by omega : N = N + ((0 : ℕ) : ℤ))).mp hbase
    | succ n ih =>
      have hnext : P (N + (n : ℤ) + 1) := by
        intro hr
        exact Hom.hom_eq_successor_of_hom_eq α β (N + (n : ℤ)) (by omega) (ih (by omega))
      exact (congrArg P (by omega : N + (n : ℤ) + 1 = N + ((n + 1 : ℕ) : ℤ))).mp hnext
  exact hall n (by omega)

/-- Equality at one page determines every later page map.

For N≤r above the starting page, α_N=β_N implies α_r=β_r. -/
theorem Hom.hom_eq_at_later_page (α β : S ⟶ T) (N : ℤ) (hN : r₀ ≤ N)
    (h : α.hom N hN = β.hom N hN) (r : ℤ) (hNr : N ≤ r) :
    α.hom r (by omega) = β.hom r (by omega) := by
  let P : ℤ → Prop := fun r ↦ ∀ hr : r₀ ≤ r, α.hom r hr = β.hom r hr
  have hr : N + ((r - N).toNat : ℤ) = r := by omega
  have hn : P (N + ((r - N).toNat : ℤ)) := by
    intro hr
    exact Hom.hom_eq_add_nat_of_hom_eq α β N hN h (r - N).toNat
  exact ((congrArg P hr).mp hn) (by omega)

/-- Equality at one page determines every later component map.

Under page equality at N, the component of α_r equals that of β_r at every index for r≥N. -/
theorem Hom.hom_f_eq_at_later_page (α β : S ⟶ T) (N : ℤ) (hN : r₀ ≤ N)
    (h : α.hom N hN = β.hom N hN) (r : ℤ) (hNr : N ≤ r) (i : ι) :
    (α.hom r (by omega)).f i = (β.hom r (by omega)).f i :=
  congrArg (fun f ↦ f.f i) (Hom.hom_eq_at_later_page α β N hN h r hNr)

end CategoryTheory.SpectralSequence


end
