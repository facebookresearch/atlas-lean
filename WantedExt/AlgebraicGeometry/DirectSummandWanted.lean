/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Direct summand theorem and derived variant

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.AlgebraicGeometry.DirectSummand` — direct_summand (manifest `manifests/problems/direct_summand.toml`, rev 1, submitter Junyan Xu, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.AlgebraicGeometry.DirectSummandWanted` namespace. Mathematical
statements are unchanged. Source:
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.DirectSummandWanted
/-!
# Direct summand conjecture and its derived variant

Hochster's direct summand conjecture states that any finite extension of a regular
commutative ring splits as a module, which was first proved by André in 2016.
Bhatt gave a quicker proof that circumvents the perfectoid Abhyankar lemma (André's
prior work) using a quantitative form of Scholze’s Hebbarkeitssatz (the Riemann
extension theorem) for perfectoid spaces. The same idea also leads to a proof of a
derived variant of the direct summand conjecture put forth by de Jong, which states
that if A is a regular (Noetherian) ring and X ⟶ Spec A is proper and surjective,
then A ⟶ RΓ(X, 𝒪_X) splits in the derived category D(A).

## References

* Yves André, La conjecture du facteur direct, https://arxiv.org/abs/1609.00345
* Bhargav Bhatt, On the direct summand conjecture and its derived variant, https://arxiv.org/abs/1608.08882
* Linquan Ma, a short proof of the direct summand theorem via the flatness lemma, https://www.math.purdue.edu/~ma326/DSC.pdf
-/

open CategoryTheory _root_.AlgebraicGeometry

open scoped _root_.AlgebraicGeometry

namespace AlgebraicGeometry.DirectSummand

variable (A : Type*) [CommRing A] [IsRegularRing A]

noncomputable def singleFunctorMapHomotopyCategory {W₁ W₂ : Type*} [Category* W₁] [Category* W₂]
    [Preadditive W₁] [Preadditive W₂] [Limits.HasZeroObject W₁] [Limits.HasZeroObject W₂]
    (F : W₁ ⥤ W₂) [F.Additive] (n : ℤ) :
    HomotopyCategory.singleFunctor W₁ n ⋙ F.mapHomotopyCategory _ ≅
    F ⋙ HomotopyCategory.singleFunctor W₂ n :=
  Functor.associator .. ≪≫ Functor.isoWhiskerLeft _ (F.mapHomotopyCategoryFactors _) ≪≫
    (Functor.associator ..).symm ≪≫
    Functor.isoWhiskerRight (HomologicalComplex.singleMapHomologicalComplex F ..) _

noncomputable def singleFunctorMapHomotopyCategoryPlus {W₁ W₂ : Type*} [Category* W₁] [Category* W₂]
    [Preadditive W₁] [Preadditive W₂] [Limits.HasZeroObject W₁] [Limits.HasZeroObject W₂]
    (F : W₁ ⥤ W₂) [F.Additive] (n : ℤ) :
    HomotopyCategory.Plus.singleFunctor W₁ n ⋙ F.mapHomotopyCategoryPlus ≅
    F ⋙ HomotopyCategory.Plus.singleFunctor W₂ n :=
  NatIso.ofComponents
    (fun X ↦ ObjectProperty.isoMk _ <| (singleFunctorMapHomotopyCategory F n).app X) <| by
    intros; ext; exact (singleFunctorMapHomotopyCategory F n).hom.naturality _

/-- The bounded-below single functor is induced by the homotopy-category single functor. -/
noncomputable def singleFunctorPlusIsoCompQh {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (n : ℤ) :
    DerivedCategory.Plus.singleFunctor C n ≅
      HomotopyCategory.Plus.singleFunctor C n ⋙ DerivedCategory.Plus.Qh :=
  (DerivedCategory.TStructure.t.plus.fullyFaithfulι.whiskeringRight C).preimageIso
    (DerivedCategory.Plus.singleFunctorιIso C n ≪≫
      DerivedCategory.singleFunctorIsoCompQh C n ≪≫
      (Functor.isoWhiskerLeft (HomotopyCategory.Plus.singleFunctor C n)
        (DerivedCategory.Plus.QhCompιIsoιCompQh C)).symm ≪≫
      (Functor.associator _ _ _).symm)

noncomputable def rightDerivedFunctorPlusUnit' {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [EnoughInjectives C] (n : ℤ) :
    F ⋙ DerivedCategory.Plus.singleFunctor _ n ⟶
    DerivedCategory.Plus.singleFunctor _ n ⋙ F.rightDerivedFunctorPlus :=
  (Functor.isoWhiskerLeft F (singleFunctorPlusIsoCompQh n)).hom ≫
    Functor.whiskerRight (singleFunctorMapHomotopyCategoryPlus F n).inv
      DerivedCategory.Plus.Qh ≫
    (HomotopyCategory.Plus.singleFunctor C n).whiskerLeft
      F.rightDerivedFunctorPlusUnith ≫
    (Functor.isoWhiskerRight (singleFunctorPlusIsoCompQh n).symm
      F.rightDerivedFunctorPlus).hom

instance {C : Type*} [Category* C] {J : GrothendieckTopology C} (R : Sheaf J RingCat) (X : Cᵒᵖ) :
    (SheafOfModules.evaluation R X).Additive where
  map_add := rfl

/-- The composite of evaluation at `⊤` with restriction of scalars is additive. Both factors
are additive, but the generic `Functor.Additive` instance for a composite does not fire at this
elaborated form, so state it directly. -/
instance (X : Scheme) {S : Type*} [Ring S] (φ : S →+* Γ(X, ⊤)) :
    (SheafOfModules.evaluation X.ringCatSheaf ⟨⊤⟩ ⋙ ModuleCat.restrictScalars φ).Additive :=
  ⟨rfl⟩

/-- Source: see manifest Via leanprover/lean-eval@38361be, problem `direct_summand`. -/
public theorem_wanted derived_direct_summand [HasDerivedCategory (ModuleCat A)]
    (X : Scheme) (f : X ⟶ Spec (.of A)) [IsProper f] (surj : Function.Surjective f)
    [HasDerivedCategory (SheafOfModules X.ringCatSheaf)] :
    let φ : A →+* Γ(X, ⊤) := ((ΓSpec.adjunction.homEquiv _ _).symm f).unop.hom
    let : Algebra A Γ(X, ⊤) := φ.toAlgebra
    ∀ _ : EnoughInjectives (SheafOfModules X.ringCatSheaf), IsSplitMono <|
      (DerivedCategory.Plus.singleFunctor _ 0).map
        (ModuleCat.ofHom (Algebra.linearMap A Γ(X, ⊤))) ≫
      (rightDerivedFunctorPlusUnit' (SheafOfModules.evaluation X.ringCatSheaf ⟨⊤⟩ ⋙
        ModuleCat.restrictScalars φ) 0).app (SheafOfModules.unit X.ringCatSheaf)

/-- Source: see manifest Via leanprover/lean-eval@38361be, problem `direct_summand`. -/
public theorem_wanted direct_summand (B : Type*) [CommRing B] [Algebra A B]
    [Module.Finite A B] [FaithfulSMul A B] :
    ∃ π : B →ₗ[A] A, π ∘ₗ Algebra.linearMap A B = .id

end AlgebraicGeometry.DirectSummand

end MathlibExt.AlgebraicGeometry.DirectSummandWanted
