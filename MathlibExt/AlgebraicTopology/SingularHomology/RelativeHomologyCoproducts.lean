/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SingularHomology.RelativeCoproducts
public import MathlibExt.AlgebraicTopology.SingularHomology.HomologyCoproducts

/-!
# Coproducts in relative singular homology

Relative singular homology preserves discrete coproducts for abelian
coefficient categories satisfying the stated AB4 condition. For additive
commutative group coefficients, explicit coproduct comparison isomorphisms are
constructed and their maps are characterized on each coproduct inclusion.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicTopology

universe w v u

/-- The relative singular homology functor preserves discrete coproducts. -/
noncomputable instance relativeSingularHomologyFunctor_preservesColimitsOfShape_discrete
    {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
    [AB4OfSize.{w} C] {J : Type w} (R : C) (n : Nat) :
    PreservesColimitsOfShape (Discrete J)
      (relativeSingularHomologyFunctor C R n) := by
  have : PreservesFiniteLimits (colim (J := Discrete J) (C := C)) :=
    inferInstance
  have : PreservesFiniteColimits (colim (J := Discrete J) (C := C)) :=
    inferInstance
  have : (colim (J := Discrete J) (C := C)).PreservesHomology :=
    inferInstance
  change PreservesColimitsOfShape (Discrete J)
    (relativeSingularChainFunctor C R ⋙
      HomologicalComplex.homologyFunctor
        C (ComplexShape.down Nat) n)
  infer_instance

/-- Coproduct comparison iso for relative singular homology. -/
noncomputable def relativeSingularHomologyCoproductIso {J : Type w}
    (P : J -> TopPair.{w}) (R : AddCommGrpCat.{w}) (n : Nat) :
    (Limits.sigmaObj fun j =>
        (relativeSingularHomologyFunctor AddCommGrpCat.{w} R n).obj (P j)) ≅
      (relativeSingularHomologyFunctor AddCommGrpCat.{w} R n).obj
        (Limits.sigmaObj P) :=
  (PreservesCoproduct.iso
    (relativeSingularHomologyFunctor AddCommGrpCat.{w} R n) P).symm

/-- Compatibility of the coproduct iso with coproduct injections. -/
@[reassoc (attr := simp)]
theorem relativeSingularHomologyCoproductIso_hom_ι {J : Type w}
    (P : J -> TopPair.{w}) (R : AddCommGrpCat.{w}) (n : Nat) (j : J) :
    Sigma.ι
          (fun j =>
            (relativeSingularHomologyFunctor AddCommGrpCat.{w} R n).obj (P j))
          j ≫
        (relativeSingularHomologyCoproductIso P R n).hom =
      (relativeSingularHomologyFunctor AddCommGrpCat.{w} R n).map
        (Sigma.ι P j) := by
  simp only [relativeSingularHomologyCoproductIso]
  have h :
      (PreservesCoproduct.iso
        (relativeSingularHomologyFunctor AddCommGrpCat.{w} R n) P).symm.hom =
        (PreservesCoproduct.iso
          (relativeSingularHomologyFunctor AddCommGrpCat.{w} R n) P).inv :=
    rfl
  rw [h, PreservesCoproduct.inv_hom]
  exact Limits.ι_comp_sigmaComparison
    (relativeSingularHomologyFunctor AddCommGrpCat.{w} R n) P j

/-- Explicit sigma coproduct comparison iso for relative singular homology, obtained as the
composite of the categorical coproduct iso and the explicit-to-categorical comparison. -/
noncomputable def relativeSingularHomologySigmaIso {J : Type w}
    (P : J → TopPair.{w}) (R : AddCommGrpCat.{w}) (n : Nat) :
    (∐ fun j =>
        (relativeSingularHomologyFunctor AddCommGrpCat.{w} R n).obj (P j)) ≅
      (relativeSingularHomologyFunctor AddCommGrpCat.{w} R n).obj
        (TopPair.sigma P) :=
  TopPair.mapSigmaIso P
    (relativeSingularHomologyFunctor AddCommGrpCat.{w} R n)

/-- Compatibility of the explicit sigma iso with coproduct injections. -/
@[reassoc (attr := simp)]
theorem relativeSingularHomologySigmaIso_hom_ι {J : Type w}
    (P : J → TopPair.{w}) (R : AddCommGrpCat.{w}) (n : Nat) (j : J) :
    @Eq ((relativeSingularHomologyFunctor AddCommGrpCat.{w} R n).obj (P j) ⟶
      (relativeSingularHomologyFunctor AddCommGrpCat.{w} R n).obj
        (TopPair.sigma P))
      (Sigma.ι (fun j =>
        (relativeSingularHomologyFunctor AddCommGrpCat.{w} R n).obj (P j)) j ≫
        (relativeSingularHomologySigmaIso P R n).hom)
      ((relativeSingularHomologyFunctor AddCommGrpCat.{w} R n).map
        (TopPair.sigmaι P j)) :=
  TopPair.mapSigmaIso_hom_ι P
    (relativeSingularHomologyFunctor AddCommGrpCat.{w} R n) j

end AlgebraicTopology
