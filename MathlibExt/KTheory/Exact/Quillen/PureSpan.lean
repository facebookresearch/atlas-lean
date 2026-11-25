/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.KTheory.Exact.Quillen.Basic

/-!
# Pure admissible spans and their Quillen arrow classes

The original admissible mono and epi keep their apex, given map and identity leg.
Their original quotient arrows compose in the forward mono and reverse epi order.
Every original admissible span factors as its pure epi followed by its pure mono.
-/

universe u v

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

namespace AlgebraicKTheory.QuillenQ

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The pure admissible mono has the original source as apex and identity left leg. -/
def pureMonoSpan {M X : C} (mu : M ⟶ X) (hmu : IsAdmissibleMono mu) :
    QuillenSpan M X where
  apex := M
  l := 𝟙 M
  r := mu
  wl := IsAdmissibleEpi.id M
  wr := hmu

/-- The pure admissible epi reverses the given arrow and keeps its apex and identity right leg. -/
def pureEpiSpan {M X : C} (lambda : M ⟶ X) (hlambda : IsAdmissibleEpi lambda) :
    QuillenSpan X M where
  apex := M
  l := lambda
  r := 𝟙 M
  wl := hlambda
  wr := IsAdmissibleMono.id M

/-- The original pure mono is a covariant arrow of the actual quotient Q category. -/
def pureMonoHom {M X : C} (mu : M ⟶ X) (hmu : IsAdmissibleMono mu) :
    (⟨M⟩ : QuillenQ C) ⟶ (⟨X⟩ : QuillenQ C) :=
  mkHom (X := ⟨M⟩) (Y := ⟨X⟩) (pureMonoSpan mu hmu)

/-- The original pure epi is a contravariant arrow of the actual quotient Q category. -/
def pureEpiHom {M X : C} (lambda : M ⟶ X) (hlambda : IsAdmissibleEpi lambda) :
    (⟨X⟩ : QuillenQ C) ⟶ (⟨M⟩ : QuillenQ C) :=
  mkHom (X := ⟨X⟩) (Y := ⟨M⟩) (pureEpiSpan lambda hlambda)

/-- Pure admissible monos compose with the original forward order in Q. -/
theorem pureMonoHom_comp {A B X : C} (mu : A ⟶ B) (nu : B ⟶ X)
    (hmu : IsAdmissibleMono mu) (hnu : IsAdmissibleMono nu) :
    pureMonoHom mu hmu ≫ pureMonoHom nu hnu =
      pureMonoHom (mu ≫ nu) (admissibleMono_comp.comp_mem mu nu hmu hnu) := by
  change quillenComp
      (mkHom (X := ⟨A⟩) (Y := ⟨B⟩) (pureMonoSpan mu hmu))
      (mkHom (X := ⟨B⟩) (Y := ⟨X⟩) (pureMonoSpan nu hnu)) =
    mkHom (X := ⟨A⟩) (Y := ⟨X⟩)
      (pureMonoSpan (mu ≫ nu) (admissibleMono_comp.comp_mem mu nu hmu hnu))
  rw [mkHom_comp]
  refine mkHom_sound (X := ⟨A⟩) (Y := ⟨X⟩) ?_
  let S : QuillenSpan A B := pureMonoSpan mu hmu
  let T : QuillenSpan B X := pureMonoSpan nu hnu
  let pL : (Span.comp S T).apex ⟶ S.apex :=
    Span.SpanBicat.πₗ (C := C) (X := ⟨A⟩) (Y := ⟨B⟩) (Z := ⟨X⟩) S T
  let pR : (Span.comp S T).apex ⟶ T.apex :=
    Span.SpanBicat.πᵣ (C := C) (X := ⟨A⟩) (Y := ⟨B⟩) (Z := ⟨X⟩) S T
  have hP : IsPullback pL pR S.r T.l :=
    IsPullback.of_isLimit
      (Span.SpanBicat.isLimitCompPullbackCone (C := C)
        (X := ⟨A⟩) (Y := ⟨B⟩) (Z := ⟨X⟩) S T)
  let _ : IsIso pL := hP.isIso_fst_of_isIso (by
    change IsIso (𝟙 B)
    infer_instance)
  let e : (Span.comp S T).apex ≅ S.apex := asIso pL
  have hE : e.hom = pL := asIso_hom pL
  have hL : (Span.comp S T).l = pL ≫ S.l :=
    Span.SpanBicat.comp_l (C := C) (X := ⟨A⟩) (Y := ⟨B⟩) (Z := ⟨X⟩) S T
  have hR : (Span.comp S T).r = pR ≫ T.r :=
    Span.SpanBicat.comp_r (C := C) (X := ⟨A⟩) (Y := ⟨B⟩) (Z := ⟨X⟩) S T
  have hC : pL ≫ S.r = pR ≫ T.l :=
    Span.SpanBicat.comp_comm (C := C) (X := ⟨A⟩) (Y := ⟨B⟩) (Z := ⟨X⟩) S T
  have h : pL ≫ mu = pR := by
    change pL ≫ mu = pR ≫ 𝟙 B at hC
    exact hC.trans (Category.comp_id pR)
  refine Span.mkIso e ?_ ?_
  · calc
      e.hom ≫ (pureMonoSpan (mu ≫ nu)
          (admissibleMono_comp.comp_mem mu nu hmu hnu)).l = pL ≫ S.l :=
        congrArg (fun q => q ≫ S.l) hE
      _ = (Span.comp S T).l := hL.symm
  · calc
      e.hom ≫ (pureMonoSpan (mu ≫ nu)
          (admissibleMono_comp.comp_mem mu nu hmu hnu)).r = pL ≫ (mu ≫ nu) :=
        congrArg (fun q => q ≫ (mu ≫ nu)) hE
      _ = (pL ≫ mu) ≫ nu := (Category.assoc pL mu nu).symm
      _ = pR ≫ nu := congrArg (fun q => q ≫ nu) h
      _ = (Span.comp S T).r := hR.symm


/-- Pure admissible epis compose with the original reverse order in Q. -/
theorem pureEpiHom_comp {A B X : C} (rho : A ⟶ B) (lambda : B ⟶ X)
    (hrho : IsAdmissibleEpi rho) (hlambda : IsAdmissibleEpi lambda) :
    pureEpiHom lambda hlambda ≫ pureEpiHom rho hrho =
      pureEpiHom (rho ≫ lambda) (admissibleEpi_comp.comp_mem rho lambda hrho hlambda) := by
  change quillenComp
      (mkHom (X := ⟨X⟩) (Y := ⟨B⟩) (pureEpiSpan lambda hlambda))
      (mkHom (X := ⟨B⟩) (Y := ⟨A⟩) (pureEpiSpan rho hrho)) =
    mkHom (X := ⟨X⟩) (Y := ⟨A⟩)
      (pureEpiSpan (rho ≫ lambda) (admissibleEpi_comp.comp_mem rho lambda hrho hlambda))
  rw [mkHom_comp]
  refine mkHom_sound (X := ⟨X⟩) (Y := ⟨A⟩) ?_
  let S : QuillenSpan X B := pureEpiSpan lambda hlambda
  let T : QuillenSpan B A := pureEpiSpan rho hrho
  let pL : (Span.comp S T).apex ⟶ S.apex :=
    Span.SpanBicat.πₗ (C := C) (X := ⟨X⟩) (Y := ⟨B⟩) (Z := ⟨A⟩) S T
  let pR : (Span.comp S T).apex ⟶ T.apex :=
    Span.SpanBicat.πᵣ (C := C) (X := ⟨X⟩) (Y := ⟨B⟩) (Z := ⟨A⟩) S T
  have hP : IsPullback pL pR S.r T.l :=
    IsPullback.of_isLimit
      (Span.SpanBicat.isLimitCompPullbackCone (C := C)
        (X := ⟨X⟩) (Y := ⟨B⟩) (Z := ⟨A⟩) S T)
  let _ : IsIso pR := hP.isIso_snd_of_isIso (by
    change IsIso (𝟙 B)
    infer_instance)
  let e : (Span.comp S T).apex ≅ T.apex := asIso pR
  have hE : e.hom = pR := asIso_hom pR
  have hL : (Span.comp S T).l = pL ≫ S.l :=
    Span.SpanBicat.comp_l (C := C) (X := ⟨X⟩) (Y := ⟨B⟩) (Z := ⟨A⟩) S T
  have hR : (Span.comp S T).r = pR ≫ T.r :=
    Span.SpanBicat.comp_r (C := C) (X := ⟨X⟩) (Y := ⟨B⟩) (Z := ⟨A⟩) S T
  have hC : pL ≫ S.r = pR ≫ T.l :=
    Span.SpanBicat.comp_comm (C := C) (X := ⟨X⟩) (Y := ⟨B⟩) (Z := ⟨A⟩) S T
  have h : pR ≫ rho = pL := by
    change pL ≫ 𝟙 B = pR ≫ rho at hC
    exact hC.symm.trans (Category.comp_id pL)
  refine Span.mkIso e ?_ ?_
  · calc
      e.hom ≫ (pureEpiSpan (rho ≫ lambda)
          (admissibleEpi_comp.comp_mem rho lambda hrho hlambda)).l = pR ≫ (rho ≫ lambda) :=
        congrArg (fun q => q ≫ (rho ≫ lambda)) hE
      _ = (pR ≫ rho) ≫ lambda := (Category.assoc pR rho lambda).symm
      _ = pL ≫ lambda := congrArg (fun q => q ≫ lambda) h
      _ = (Span.comp S T).l := hL.symm
  · calc
      e.hom ≫ (pureEpiSpan (rho ≫ lambda)
          (admissibleEpi_comp.comp_mem rho lambda hrho hlambda)).r = pR ≫ T.r :=
        congrArg (fun q => q ≫ T.r) hE
      _ = (Span.comp S T).r := hR.symm


/-- Every original admissible span factors as its pure epi followed by its pure mono. -/
theorem pureEpiHom_pureMonoHom {X Y : C} (sigma : QuillenSpan X Y) :
    pureEpiHom sigma.l sigma.wl ≫ pureMonoHom sigma.r sigma.wr =
      mkHom (X := ⟨X⟩) (Y := ⟨Y⟩) sigma := by
  change quillenComp
      (mkHom (X := ⟨X⟩) (Y := ⟨sigma.apex⟩) (pureEpiSpan sigma.l sigma.wl))
      (mkHom (X := ⟨sigma.apex⟩) (Y := ⟨Y⟩) (pureMonoSpan sigma.r sigma.wr)) =
    mkHom (X := ⟨X⟩) (Y := ⟨Y⟩) sigma
  rw [mkHom_comp]
  refine mkHom_sound (X := ⟨X⟩) (Y := ⟨Y⟩) ?_
  let S : QuillenSpan X sigma.apex := pureEpiSpan sigma.l sigma.wl
  let T : QuillenSpan sigma.apex Y := pureMonoSpan sigma.r sigma.wr
  let pL : (Span.comp S T).apex ⟶ S.apex :=
    Span.SpanBicat.πₗ (C := C) (X := ⟨X⟩) (Y := ⟨sigma.apex⟩) (Z := ⟨Y⟩) S T
  let pR : (Span.comp S T).apex ⟶ T.apex :=
    Span.SpanBicat.πᵣ (C := C) (X := ⟨X⟩) (Y := ⟨sigma.apex⟩) (Z := ⟨Y⟩) S T
  have hP : IsPullback pL pR S.r T.l :=
    IsPullback.of_isLimit
      (Span.SpanBicat.isLimitCompPullbackCone (C := C)
        (X := ⟨X⟩) (Y := ⟨sigma.apex⟩) (Z := ⟨Y⟩) S T)
  let _ : IsIso pL := hP.isIso_fst_of_isIso (by
    change IsIso (𝟙 sigma.apex)
    infer_instance)
  let e : (Span.comp S T).apex ≅ S.apex := asIso pL
  have hE : e.hom = pL := asIso_hom pL
  have hL : (Span.comp S T).l = pL ≫ S.l :=
    Span.SpanBicat.comp_l (C := C) (X := ⟨X⟩) (Y := ⟨sigma.apex⟩) (Z := ⟨Y⟩) S T
  have hR : (Span.comp S T).r = pR ≫ T.r :=
    Span.SpanBicat.comp_r (C := C) (X := ⟨X⟩) (Y := ⟨sigma.apex⟩) (Z := ⟨Y⟩) S T
  have hC : pL ≫ S.r = pR ≫ T.l :=
    Span.SpanBicat.comp_comm (C := C) (X := ⟨X⟩) (Y := ⟨sigma.apex⟩) (Z := ⟨Y⟩) S T
  have h : pL = pR := by
    change pL ≫ 𝟙 sigma.apex = pR ≫ 𝟙 sigma.apex at hC
    exact (Category.comp_id pL).symm.trans (hC.trans (Category.comp_id pR))
  refine Span.mkIso e ?_ ?_
  · calc
      e.hom ≫ sigma.l = pL ≫ S.l := congrArg (fun q => q ≫ S.l) hE
      _ = (Span.comp S T).l := hL.symm
  · calc
      e.hom ≫ sigma.r = pL ≫ sigma.r := congrArg (fun q => q ≫ sigma.r) hE
      _ = pR ≫ T.r := congrArg (fun q => q ≫ sigma.r) h
      _ = (Span.comp S T).r := hR.symm


end AlgebraicKTheory.QuillenQ

end
