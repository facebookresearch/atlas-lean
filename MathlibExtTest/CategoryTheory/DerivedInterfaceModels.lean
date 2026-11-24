/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Algebra.Homology.GradedMixedCochainModels
public import MathlibExt.CategoryTheory.DGQuasiFunctorModels

@[expose] public noncomputable section

namespace MathlibExtTest.CategoryTheory.DerivedInterfaceModels

open _root_.CategoryTheory CochainComplex CochainComplex.HomComplex
open MathlibExt.Algebra.Homology.GradedMixedCochainModels
open MathlibExt.CategoryTheory.DGQuasiFunctorModels

abbrev flat : CochainComplex (ModuleCat ℚ) ℤ where
  X _ := ModuleCat.of ℚ ℚ
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ := by simp

def eps (w : ℤ) : Cochain flat flat (-1) :=
  if w = 0 then Cochain.mk (fun _ _ _ => 𝟙 (ModuleCat.of ℚ ℚ)) else 0

abbrev mixed : GradedMixed ℚ where
  weight _ := flat
  epsilon := eps
  closed w := by
    apply Cochain.ext
    intro p q h
    simp [δ, flat, Cochain.v, Cochain.mk]
    rfl
  square w := by
    by_cases h : w = 0
    · subst w
      simp [eps]
    · simp [eps, h]

def seed : Coefficients mixed 0 0 := by
  change ℕ → ℚ
  exact fun i => if i = 0 then 1 else 0

-- The incoming mixed term really contributes in the next weight; the
-- normalized operator cannot be an all-zero placeholder.
example : (differential mixed 0 0 seed 1 : ℚ) = 1 := by
  change (0 : ℚ) + seed 0 = 1
  simp [seed]

example : (differential mixed 0 0 seed 0 : ℚ) = 0 := by
  change (0 : ℚ) + 0 = 0
  norm_num

-- The canonical point-evaluation provider is usable with the actual
-- variance of the graph/Yoneda columns.
example {C D : Type} [MathlibExt.DGSource.DGCategory ℚ C]
    [MathlibExt.DGSource.DGCategory ℚ D]
    (f : EnrichedFunctor
      (MathlibExt.CategoryTheory.DGModelContracts.Cochains ℚ) C D) :
    IsRightQuasiRepresentable (fun y => canonicalEvaluation (k := ℚ) y) (graph f) :=
  graph_isRightQuasiRepresentable _ f

-- A C-morphism acts forward on right-D-module columns. This fails for
-- the opposite/corepresentable variant and checks the source variance.
example {C D : Type} [MathlibExt.DGSource.DGCategory ℚ C]
    [MathlibExt.DGSource.DGCategory ℚ D]
    (f : EnrichedFunctor
      (MathlibExt.CategoryTheory.DGModelContracts.Cochains ℚ) C D)
    (x y : C) (a : MathlibExt.DGSource.DGHom ℚ 0 x y) :
    MathlibExt.DGSource.DGHom ℚ 0
      ((graph f).toEnrichedFunctor.obj x) ((graph f).toEnrichedFunctor.obj y) :=
  (graph f).toEnrichedFunctor.dgMap 0 a

#check MathlibExt.CategoryTheory.DGModelContracts.LocalizedTensorModel
#check MathlibExt.CategoryTheory.DGQuasiFunctorModels.DGDerivedModules

end MathlibExtTest.CategoryTheory.DerivedInterfaceModels
