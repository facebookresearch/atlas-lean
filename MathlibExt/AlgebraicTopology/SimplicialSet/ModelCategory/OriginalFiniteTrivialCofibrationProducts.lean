/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BetaPairTrivialCofibration
import MathlibExt.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Actual finite TCof products without fibrancy hypotheses

The same chosen Fin n product map is identified with a head/tail binary
product by a constructed whole Iso. Native tensor-left Quillen preservation
and braiding give binary TCof stability; induction covers every Fin n,
including Fin 0. Raw simplicial sets need no Kan hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SSet

/-- Every actual finite product of TCof maps is TCof. The empty product is
the native identity of the same chosen empty product, not a chosen vertex. -/
theorem trivialCofibration_finite_Pi_map (n : ℕ)
    {X Y : Fin n → SSet.{u}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, trivialCofibrations SSet.{u} (f i)) :
    trivialCofibrations SSet.{u} (CategoryTheory.Limits.Pi.map f) := by
  induction n with
  | zero =>
      let : IsIso (CategoryTheory.Limits.Pi.map f) := by
        refine ⟨⟨CategoryTheory.Limits.Pi.lift (fun i => Fin.elim0 i), ?_, ?_⟩⟩
        · apply CategoryTheory.Limits.Pi.hom_ext
          intro i
          exact Fin.elim0 i
        · apply CategoryTheory.Limits.Pi.hom_ext
          intro i
          exact Fin.elim0 i
      exact (mem_trivialCofibrations_iff _).mpr
        ⟨inferInstanceAs (Cofibration (CategoryTheory.Limits.Pi.map f)),
            inferInstanceAs (WeakEquivalence (CategoryTheory.Limits.Pi.map f))⟩
  | succ n ih =>
      have ht := ih (fun i : Fin n => f i.succ) (fun i => hf i.succ)
      have hb := trivialCofibration_prodMap (f 0)
          (CategoryTheory.Limits.Pi.map (fun i : Fin n => f i.succ)) (hf 0) ht
      exact ((trivialCofibrations SSet.{u}).arrow_mk_iso_iff
        (CategoryTheory.Limits.Pi.finSuccProductArrowIso n f)).mpr hb

/-- In particular, the SAME baseline beta on every raw object factor is weak
in all finite arities, with no RawW₀ Kan or full-Unit9 weakness assumption. -/
theorem betaFiniteProduct_realizationWeak (n : ℕ) {R H : SSet.{u}} (β : R ⟶ H)
    (hβ : trivialCofibrations SSet.{u} β) :
    realizationWeakEquivalences (CategoryTheory.Limits.Pi.map (fun _ : Fin n => β)) :=
  (weakEquivalence_iff _).mp
    ((mem_trivialCofibrations_iff _).mp
      (trivialCofibration_finite_Pi_map n (fun _ : Fin n => β) (fun _ => hβ))).2

end SSet
