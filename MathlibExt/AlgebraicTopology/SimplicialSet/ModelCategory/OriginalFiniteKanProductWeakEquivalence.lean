/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWProduct
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BoundaryRLPRealizationWeakEquivalence
import MathlibExt.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Finite products of Kan weak equivalences

The chosen product map indexed by `Fin n` preserves `KanComplex.W`, including the empty product. For families of Kan complexes, componentwise realization weak equivalences therefore give a realization weak equivalence of the full product map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SSet.OriginalFiniteKanProducts


private def finZeroProductIsTerminal (X : Fin 0 → SSet.{u}) : IsTerminal (∏ᶜ X) :=
  IsTerminal.ofUniqueHom
    (fun _ => CategoryTheory.Limits.Pi.lift fun i => Fin.elim0 i)
    (fun _ _ => by apply CategoryTheory.Limits.Pi.hom_ext; intro i; exact Fin.elim0 i)

private theorem finZeroProductKan (X : Fin 0 → SSet.{u}) : KanComplex (∏ᶜ X) := by
  let e := (finZeroProductIsTerminal X).uniqueUpToIso terminalIsTerminal
  have h : terminal.from (∏ᶜ X) = e.hom := Subsingleton.elim _ _
  change Fibration (terminal.from (∏ᶜ X))
  rw [h]
  infer_instance

/-- Finite chosen products preserve the full Kan weak-equivalence predicate. -/
theorem W.finPiMap (n : ℕ) (X Y : Fin n → SSet.{u})
    (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, KanComplex.W (f i)) :
    KanComplex.W (CategoryTheory.Limits.Pi.map f) := by
  induction n with
  | zero =>
      let : KanComplex (∏ᶜ X) := finZeroProductKan X
      let : KanComplex (∏ᶜ Y) := finZeroProductKan Y
      let : ∀ i : Fin 0, IsIso (f i) := fun i => Fin.elim0 i
      exact KanComplex.W.ofIso (asIso (CategoryTheory.Limits.Pi.map f))
  | succ n ih =>
      let fTail : ∀ i : Fin n, X i.succ ⟶ Y i.succ := fun i => f i.succ
      have hTail : KanComplex.W (CategoryTheory.Limits.Pi.map fTail) :=
        ih (fun i => X i.succ) (fun i => Y i.succ) fTail (fun i => hf i.succ)
      have hBinary : KanComplex.W (prod.map (f 0) (CategoryTheory.Limits.Pi.map fTail)) :=
        KanComplex.W.prodMap (hf 0) hTail
      let e : Arrow.mk (CategoryTheory.Limits.Pi.map f) ≅
          Arrow.mk (prod.map (f 0) (CategoryTheory.Limits.Pi.map fTail)) :=
        CategoryTheory.Limits.Pi.finSuccProductArrowIso n f
      exact (MorphismProperty.arrow_mk_iso_iff KanComplex.W e).mpr hBinary

/-- For arbitrary Kan factors, the literal finite product map is a realization weak equivalence. -/
theorem realizationWeakEquivalence_finPiMap (n : ℕ)
    (X Y : Fin n → SSet.{u}) [∀ i, KanComplex (X i)] [∀ i, KanComplex (Y i)]
    (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, realizationWeakEquivalences (f i)) :
    realizationWeakEquivalences (CategoryTheory.Limits.Pi.map f) := by
  have h : KanComplex.W (CategoryTheory.Limits.Pi.map f) := W.finPiMap n X Y f
    (fun i => (KanComplex.W_iff_realizationWeakEquivalence (f i)).mpr (hf i))
  let : KanComplex (∏ᶜ X) := h.kanComplex_source
  let : KanComplex (∏ᶜ Y) := h.kanComplex_target
  exact (KanComplex.W_iff_realizationWeakEquivalence (CategoryTheory.Limits.Pi.map f)).mp h

end SSet.OriginalFiniteKanProducts
