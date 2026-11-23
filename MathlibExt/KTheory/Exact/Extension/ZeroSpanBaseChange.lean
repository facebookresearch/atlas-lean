/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.LocalizedBaseChangeComposition
public import MathlibExt.KTheory.Exact.Quillen.PureSpan

/-!
# The original zero-span and admissible-span base-change triangles

Pure admissible monos and epis retain their identity leg and given original map.
Pullback projections provide the actual apex isomorphisms for their quotient equations.
The two zero-span constructors keep their zero-apex and given-object-apex formulas.
The resulting functor triangles use the chosen localized pullbacks in reverse order.
-/

universe u v

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject

namespace AlgebraicKTheory.QuillenQ

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The zero-apex span followed by a pure mono is the same original zero-apex Q arrow. -/
theorem zeroMonoHom_pureMonoHom {M X : C} (mu : M ⟶ X) (hmu : IsAdmissibleMono mu) :
    ExtensionCategory.zeroMonoHom M ≫ pureMonoHom mu hmu =
      ExtensionCategory.zeroMonoHom X := by
  change quillenComp
      (mkHom (X := ⟨0⟩) (Y := ⟨M⟩) (ExtensionCategory.zeroMonoSpan M))
      (mkHom (X := ⟨M⟩) (Y := ⟨X⟩) (pureMonoSpan mu hmu)) =
    mkHom (X := ⟨0⟩) (Y := ⟨X⟩) (ExtensionCategory.zeroMonoSpan X)
  rw [mkHom_comp]
  refine mkHom_sound (X := ⟨0⟩) (Y := ⟨X⟩) ?_
  let S : QuillenSpan (0 : C) M := ExtensionCategory.zeroMonoSpan M
  let T : QuillenSpan M X := pureMonoSpan mu hmu
  let pL : (Span.comp S T).apex ⟶ S.apex :=
    Span.SpanBicat.πₗ (C := C) (X := ⟨(0 : C)⟩) (Y := ⟨M⟩) (Z := ⟨X⟩) S T
  let pR : (Span.comp S T).apex ⟶ T.apex :=
    Span.SpanBicat.πᵣ (C := C) (X := ⟨(0 : C)⟩) (Y := ⟨M⟩) (Z := ⟨X⟩) S T
  have hP : IsPullback pL pR S.r T.l :=
    IsPullback.of_isLimit
      (Span.SpanBicat.isLimitCompPullbackCone (C := C)
        (X := ⟨(0 : C)⟩) (Y := ⟨M⟩) (Z := ⟨X⟩) S T)
  let _ : IsIso pL := hP.isIso_fst_of_isIso (by
    change IsIso (𝟙 M)
    infer_instance)
  let e : (Span.comp S T).apex ≅ S.apex := asIso pL
  have hE : e.hom = pL := asIso_hom pL
  have hL : (Span.comp S T).l = pL ≫ S.l :=
    Span.SpanBicat.comp_l (C := C) (X := ⟨(0 : C)⟩) (Y := ⟨M⟩) (Z := ⟨X⟩) S T
  have hR : (Span.comp S T).r = pR ≫ T.r :=
    Span.SpanBicat.comp_r (C := C) (X := ⟨(0 : C)⟩) (Y := ⟨M⟩) (Z := ⟨X⟩) S T
  have hC : pL ≫ S.r = pR ≫ T.l :=
    Span.SpanBicat.comp_comm (C := C) (X := ⟨(0 : C)⟩) (Y := ⟨M⟩) (Z := ⟨X⟩) S T
  have h : pL ≫ (0 : (0 : C) ⟶ M) = pR := by
    change pL ≫ (0 : (0 : C) ⟶ M) = pR ≫ 𝟙 M at hC
    exact hC.trans (Category.comp_id pR)
  refine Span.mkIso e ?_ ?_
  · calc
      e.hom ≫ (ExtensionCategory.zeroMonoSpan X).l = pL ≫ S.l :=
        congrArg (fun q => q ≫ S.l) hE
      _ = (Span.comp S T).l := hL.symm
  · calc
      e.hom ≫ (ExtensionCategory.zeroMonoSpan X).r = pL ≫ (0 : (0 : C) ⟶ X) :=
        congrArg (fun q => q ≫ (0 : (0 : C) ⟶ X)) hE
      _ = pR ≫ mu := by
        have hZero : (0 : (0 : C) ⟶ M) ≫ mu = (0 : (0 : C) ⟶ X) := zero_comp
        calc
          pL ≫ (0 : (0 : C) ⟶ X) = pL ≫ ((0 : (0 : C) ⟶ M) ≫ mu) :=
            congrArg (fun q : (0 : C) ⟶ X => pL ≫ q) hZero.symm
          _ = (pL ≫ (0 : (0 : C) ⟶ M)) ≫ mu :=
            (Category.assoc pL (0 : (0 : C) ⟶ M) mu).symm
          _ = pR ≫ mu :=
            congrArg (fun q : (Span.comp S T).apex ⟶ M => q ≫ mu) h
      _ = (Span.comp S T).r := hR.symm


/-- The given-object zero span followed by a pure epi keeps the actual given-object span. -/
theorem zeroEpiHom_pureEpiHom {M X : C} (lambda : M ⟶ X)
    (hlambda : IsAdmissibleEpi lambda) :
    ExtensionCategory.zeroEpiHom X ≫ pureEpiHom lambda hlambda =
      ExtensionCategory.zeroEpiHom M := by
  change quillenComp
      (mkHom (X := ⟨0⟩) (Y := ⟨X⟩) (ExtensionCategory.zeroEpiSpan X))
      (mkHom (X := ⟨X⟩) (Y := ⟨M⟩) (pureEpiSpan lambda hlambda)) =
    mkHom (X := ⟨0⟩) (Y := ⟨M⟩) (ExtensionCategory.zeroEpiSpan M)
  rw [mkHom_comp]
  refine mkHom_sound (X := ⟨0⟩) (Y := ⟨M⟩) ?_
  let S : QuillenSpan (0 : C) X := ExtensionCategory.zeroEpiSpan X
  let T : QuillenSpan X M := pureEpiSpan lambda hlambda
  let pL : (Span.comp S T).apex ⟶ S.apex :=
    Span.SpanBicat.πₗ (C := C) (X := ⟨(0 : C)⟩) (Y := ⟨X⟩) (Z := ⟨M⟩) S T
  let pR : (Span.comp S T).apex ⟶ T.apex :=
    Span.SpanBicat.πᵣ (C := C) (X := ⟨(0 : C)⟩) (Y := ⟨X⟩) (Z := ⟨M⟩) S T
  have hP : IsPullback pL pR S.r T.l :=
    IsPullback.of_isLimit
      (Span.SpanBicat.isLimitCompPullbackCone (C := C)
        (X := ⟨(0 : C)⟩) (Y := ⟨X⟩) (Z := ⟨M⟩) S T)
  let _ : IsIso pR := hP.isIso_snd_of_isIso (by
    change IsIso (𝟙 X)
    infer_instance)
  let e : (Span.comp S T).apex ≅ T.apex := asIso pR
  have hE : e.hom = pR := asIso_hom pR
  have hL : (Span.comp S T).l = pL ≫ S.l :=
    Span.SpanBicat.comp_l (C := C) (X := ⟨(0 : C)⟩) (Y := ⟨X⟩) (Z := ⟨M⟩) S T
  have hR : (Span.comp S T).r = pR ≫ T.r :=
    Span.SpanBicat.comp_r (C := C) (X := ⟨(0 : C)⟩) (Y := ⟨X⟩) (Z := ⟨M⟩) S T
  refine Span.mkIso e ?_ ?_
  · calc
      e.hom ≫ (ExtensionCategory.zeroEpiSpan M).l = 0 := by
        change e.hom ≫ (0 : M ⟶ (0 : C)) = 0
        exact comp_zero
      _ = pL ≫ S.l := by
        change (0 : (Span.comp S T).apex ⟶ (0 : C)) = pL ≫ (0 : X ⟶ (0 : C))
        exact (comp_zero : pL ≫ (0 : X ⟶ (0 : C)) = 0).symm
      _ = (Span.comp S T).l := hL.symm
  · calc
      e.hom ≫ (ExtensionCategory.zeroEpiSpan M).r = pR ≫ T.r :=
        congrArg (fun q => q ≫ T.r) hE
      _ = (Span.comp S T).r := hR.symm


end AlgebraicKTheory.QuillenQ

namespace AlgebraicKTheory.LocalizedBaseChange

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The mono zero-span triangle is natural in every actual target-fiber object. -/
def zeroMonoPureMonoTriangleNatIso {M X : C} (mu : M ⟶ X)
    (hmu : IsAdmissibleMono mu) :
    zeroMonoBaseChange X ≅ baseChangeFunctor (QuillenQ.pureMonoHom mu hmu) ⋙
      zeroMonoBaseChange M := by
  let s : (⟨0⟩ : QuillenQ C) ⟶ (⟨M⟩ : QuillenQ C) := ExtensionCategory.zeroMonoHom M
  let m : (⟨M⟩ : QuillenQ C) ⟶ (⟨X⟩ : QuillenQ C) := QuillenQ.pureMonoHom mu hmu
  have h : s ≫ m = ExtensionCategory.zeroMonoHom X := QuillenQ.zeroMonoHom_pureMonoHom mu hmu
  let e : baseChangeFunctor (s ≫ m) ≅ zeroMonoBaseChange X :=
    eqToIso (congrArg (fun q : (⟨0⟩ : QuillenQ C) ⟶ (⟨X⟩ : QuillenQ C) =>
      baseChangeFunctor q) h)
  exact e.symm ≪≫ baseChangeCompositionNatIso s m

/-- The epi zero-span triangle keeps the given-object zero span and its reverse pullback order. -/
def zeroEpiPureEpiTriangleNatIso {M X : C} (lambda : M ⟶ X)
    (hlambda : IsAdmissibleEpi lambda) :
    zeroEpiBaseChange M ≅ baseChangeFunctor (QuillenQ.pureEpiHom lambda hlambda) ⋙
      zeroEpiBaseChange X := by
  let t : (⟨0⟩ : QuillenQ C) ⟶ (⟨X⟩ : QuillenQ C) := ExtensionCategory.zeroEpiHom X
  let e : (⟨X⟩ : QuillenQ C) ⟶ (⟨M⟩ : QuillenQ C) := QuillenQ.pureEpiHom lambda hlambda
  have h : t ≫ e = ExtensionCategory.zeroEpiHom M :=
    QuillenQ.zeroEpiHom_pureEpiHom lambda hlambda
  let i : baseChangeFunctor (t ≫ e) ≅ zeroEpiBaseChange M :=
    eqToIso (congrArg (fun q : (⟨0⟩ : QuillenQ C) ⟶ (⟨M⟩ : QuillenQ C) =>
      baseChangeFunctor q) h)
  exact i.symm ≪≫ baseChangeCompositionNatIso t e

end AlgebraicKTheory.LocalizedBaseChange

end
