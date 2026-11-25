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

public import MathlibExt.Algebra.Homology.Embedding.ExtendHomologyFunctor
public import MathlibExt.Algebra.Homology.Embedding.DownNatToInt
public import MathlibExt.Algebra.Homology.HomologyDegreeTransport

/-! Client tests for functorial degree and extension homology comparisons. -/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ v u

namespace HomologicalComplex.HomologyFunctorComparisonTests

section Degree

variable {I : Type w₁} {C : Type u} [Category.{v} C]
  [HasZeroMorphisms C] [CategoryWithHomology C]
variable {c : ComplexShape I} {p q : I} (h : p = q)

example : cyclesFunctor C c p ≅ cyclesFunctor C c q :=
  cyclesFunctorIsoOfEq h

example : opcyclesFunctor C c p ≅ opcyclesFunctor C c q :=
  opcyclesFunctorIsoOfEq h

example : homologyFunctor C c p ≅ homologyFunctor C c q :=
  homologyFunctorIsoOfEq h

example (K : HomologicalComplex C c) :
    (homologyFunctorIsoOfEq (C := C) h).hom.app K =
      (homologyIsoOfEq K h).hom :=
  homologyFunctorIsoOfEq_hom_app h K

end Degree

section Extension

variable {I : Type w₁} {J : Type w₂}
variable {c : ComplexShape I} {d : ComplexShape J}
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [CategoryWithHomology C]
variable (e : c.Embedding d) (i : I) (j : J) (h : e.f i = j)

example :
    e.extendFunctor C ⋙ cyclesFunctor C d j ≅ cyclesFunctor C c i :=
  extendCyclesFunctorIso e i j h

example :
    e.extendFunctor C ⋙ opcyclesFunctor C d j ≅ opcyclesFunctor C c i :=
  extendOpcyclesFunctorIso e i j h

example :
    e.extendFunctor C ⋙ homologyFunctor C d j ≅ homologyFunctor C c i :=
  extendHomologyFunctorIso e i j h

example {K L : HomologicalComplex C c} (φ : K ⟶ L) :
    homologyMap φ i ≫ (L.extendHomologyIso e h).inv =
      (K.extendHomologyIso e h).inv ≫ homologyMap (extendMap φ e) j :=
  extendHomologyIso_inv_naturality φ e h

example {K L : HomologicalComplex C c} (φ : K ⟶ L) :
    (K.extendXIso e h).inv ≫ (extendMap φ e).f j =
      φ.f i ≫ (L.extendXIso e h).inv :=
  extendXIso_inv_naturality e φ h

end Extension

section DownNatWeak

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C]
variable {K L : ChainComplex C ℕ} (n : ℕ)
variable [K.HasHomology n] [L.HasHomology n]
  [(K.extend ComplexShape.embeddingDownNatToInt).HasHomology (n : ℤ)]
  [(L.extend ComplexShape.embeddingDownNatToInt).HasHomology (n : ℤ)]

example :
    (K.extend ComplexShape.embeddingDownNatToInt).cycles (n : ℤ) ≅
      K.cycles n :=
  cyclesIsoExtendDownNatToInt K n

example :
    (K.extend ComplexShape.embeddingDownNatToInt).opcycles (n : ℤ) ≅
      K.opcycles n :=
  opcyclesIsoExtendDownNatToInt K n

example (φ : K ⟶ L) :
    cyclesMap (extendMap φ ComplexShape.embeddingDownNatToInt) (n : ℤ) ≫
        (cyclesIsoExtendDownNatToInt L n).hom =
      (cyclesIsoExtendDownNatToInt K n).hom ≫ cyclesMap φ n :=
  cyclesIso_extendDownNatToInt_naturality φ n

end DownNatWeak

#print axioms cyclesFunctorIsoOfEq
#print axioms opcyclesFunctorIsoOfEq
#print axioms homologyFunctorIsoOfEq
#print axioms extendCyclesFunctorIso
#print axioms extendOpcyclesFunctorIso
#print axioms extendHomologyIso_inv_naturality

end HomologicalComplex.HomologyFunctorComparisonTests

end
