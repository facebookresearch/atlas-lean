/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.AbelianImagesUltraproducts
import Mathlib.Algebra.Group.Pi.Hom
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Basic

open MathlibExt.GroupTheory.AbelianImagesUltraproductsKourovka20Problem13Wanted

-- A principal ultrafilter detects exactly one coordinate, even for nonabelian factors.
example (k : ℕ) (G : ℕ → Type) [∀ i, Group (G i)] :
    ultraproductKernel (pure k) G = (Pi.evalMonoidHom G k).ker := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    change ∀ᶠ i in ((pure k : Ultrafilter ℕ) : Filter ℕ), x i = 1 at hx
    simpa using hx
  · intro x hx
    apply Subgroup.subset_normalClosure
    change ∀ᶠ i in ((pure k : Ultrafilter ℕ) : Filter ℕ), x i = 1
    simpa using hx

-- A nonprincipal ultrafilter ignores every finite set of changed coordinates.
example (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (G : ℕ → Type) [∀ i, Group (G i)] (x y : ∀ i, G i) (h : {i | x i ≠ y i}.Finite) :
    (QuotientGroup.mk x : Ultraproduct U G) = QuotientGroup.mk y := by
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  have hxy : ∀ᶠ i in (U : Filter ℕ), x i = y i := hU (Filter.eventually_cofinite.mpr h)
  exact hxy.mono fun i hi => show (x i)⁻¹ * y i = 1 by simp [hi]

-- The input product can have nonabelian factors: project onto the cyclic component
-- in coordinate zero of a product of copies of C₂ × S₃.
example : ∃ (J : Type) (H : J → Type) (_ : ∀ j, CommGroup (H j)),
    (∀ j, Finite (H j)) ∧ ∃ ψ : (∀ j, H j) →* Multiplicative (ZMod 2),
      Function.Surjective ψ := by
  let A := Multiplicative (ZMod 2)
  have : Finite A := Finite.of_equiv (ZMod 2) Multiplicative.ofAdd
  let G (_ : ℕ) := A × Equiv.Perm (Fin 3)
  have (i : ℕ) : Finite (G i) := by
    change Finite (A × Equiv.Perm (Fin 3))
    infer_instance
  let φ : (∀ i, G i) →* A :=
    (MonoidHom.fst A (Equiv.Perm (Fin 3))).comp (Pi.evalMonoidHom G 0)
  exact abelianImageOfProductOfFiniteIsImageOfAbelianProduct_holds A ℕ G
    ⟨φ, fun a => ⟨fun _ => (a, 1), rfl⟩⟩
