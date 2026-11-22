/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.DwyerKanBrownFactorization
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.DwyerKanFibration

/-!
# Genuine one-fold Joyal Dwyer–Kan recognition

An actual map between original quasicategories is a categorical
equivalence exactly when its actual homotopy-category functor is
essentially surjective and every same-endpoint right mapping-space map
is a realization weak equivalence. The converse uses the genuine Brown
factorization and the proved full boundary-RLP criterion. No categorical
equivalence, core comparison, or extra source cofibrancy is an input.

The source theorem is D. Stevenson, *Notes on the Joyal model structure*,
[arXiv:1810.05233v1](https://arxiv.org/abs/1810.05233v1), §2.4,
Proposition 2.24 (printed page 9). His Definition 2.16 uses left mapping
spaces. This statement uses the actual join-slice right mapping spaces
and proves recognition in that model; see Lurie's *Higher Topos Theory*,
§1.2.2 for mapping-space models.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra

namespace SSet

attribute [local instance] JoyalSSet.modelCategory

variable {X Y : SSet.{u}} {f : X ⟶ Y}

/-- The actual essential-surjectivity and same-map mapping-space weakness criterion implies a genuine
  categorical equivalence between the supplied original quasicategories. -/
theorem isDwyerKanEquivalence.categoricalEquivalences [Quasicategory X] [Quasicategory Y]
    (hDK : isDwyerKanEquivalence f) : categoricalEquivalences f := by
  let _ : IsFibrant (JoyalSSet.ofSSet.obj X) :=
    (JoyalSSet.isFibrant_iff_quasicategory _).mpr (show Quasicategory X from inferInstance)
  let _ : IsFibrant (JoyalSSet.ofSSet.obj Y) :=
    (JoyalSSet.isFibrant_iff_quasicategory _).mpr (show Quasicategory Y from inferInstance)
  let h : FibrantBrownFactorization (JoyalSSet.ofSSet.map f) := Classical.choice inferInstance
  let i : X ⟶ JoyalSSet.forget.obj h.Z := JoyalSSet.forget.map h.i
  let p : JoyalSSet.forget.obj h.Z ⟶ Y := JoyalSSet.forget.map h.p
  have hfac : i ≫ p = f :=
    (JoyalSSet.forget.map_comp _ _).symm.trans
      (congrArg (fun g => JoyalSSet.forget.map g) h.fac)
  have hpFib : categoricalFibrations p := by
    have hp := (fibration_iff h.p).mp inferInstance
    change JoyalSSet.modelCategory.categoryWithFibrations.fibrations h.p at hp
    rw [JoyalSSet.modelCategory_fibrations] at hp
    exact hp
  have hpFF : SSet.dwyerKanFullyFaithful p :=
    JoyalDwyerKan.fibrantBrownFactorization_fullyFaithful f h hDK.2
  have hpES : SSet.dwyerKanEssentiallySurjective p := by
    have hc : SSet.dwyerKanEssentiallySurjective (i ≫ p) := by
      rw [hfac]
      exact hDK.1
    exact hc.of_precomp
  have hpW : SSet.categoricalEquivalences p :=
    ((categoricalFibrations_and_categoricalEquivalences_iff p).mpr
      (hpFib.mem_I_rlp_of_dwyerKan ⟨hpES, hpFF⟩)).2
  have hiW : SSet.categoricalEquivalences i := by
    let _ : WeakEquivalence h.i := ((mem_trivialCofibrations_iff (f := h.i)).mp h.hi).2
    have hi := (weakEquivalence_iff h.i).mp inferInstance
    change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences h.i at hi
    rw [JoyalSSet.modelCategory_weakEquivalences] at hi
    exact hi
  rw [← hfac]
  exact SSet.categoricalEquivalences.comp_mem i p hiW hpW

/-- Categorical equivalence is exactly the genuine same-map Dwyer–Kan criterion on original quasicategories. -/
theorem categoricalEquivalences_iff_isDwyerKanEquivalence [Quasicategory X] [Quasicategory Y] :
    categoricalEquivalences f ↔ isDwyerKanEquivalence f :=
  ⟨fun hf => hf.isDwyerKanEquivalence, fun hDK => hDK.categoricalEquivalences⟩

end SSet
