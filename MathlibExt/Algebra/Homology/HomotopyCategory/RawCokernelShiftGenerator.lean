/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomotopyCategory.HomComplexReducedFactorization
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-!
# Raw cokernel generators in degree zero

A homogeneous cochain that vanishes on an complex map descends through its cokernel, then
desuspends to a degree-zero raw cochain. Neither the input nor the output is assumed closed. Each
component descends through the evaluated cokernel cofork, then the signed left shift produces the
generator. Only cokernels in the base category are needed.

The characteristic projection–unshift law determines the whole generator. It gives inverse
reconstruction, additivity, and naturality under cokernel maps. Applying the internal Hom
differential to recovery retains the shift sign; in degree one that sign is minus one.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.HomComplex.Cochain

universe u v

variable {D : Type u} [Category.{v} D] [Preadditive D]
variable [HasCokernels D]
variable {U C A B : CochainComplex D ℤ}

/--
Precomposition by the cokernel projection is injective on raw cochains of any integer degree.
Evaluation of the cokernel cofork supplies its universal uniqueness; no component epimorphism is
assumed.
-/
theorem cokernel_precomp_injective (η : U ⟶ C) (d : ℤ) :
    let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
    Function.Injective (fun ρ : Cochain (cokernel η) A d =>
      (ofHom (cokernel.π η)).comp ρ (zero_add d)) := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  dsimp only
  intro ρ σ hρσ
  apply Cochain.ext
  intro p q hpq
  let Eₚ := HomologicalComplex.eval D (ComplexShape.up ℤ) p
  let _ : PreservesColimit (parallelPair η 0) Eₚ :=
    HomologicalComplex.eval_preservesColimit_of_hasCokernel_f η p
  let S : CokernelCofork (η.f p) :=
    (CokernelCofork.ofπ (cokernel.π η) (cokernel.condition η)).map Eₚ
  let hS : IsColimit S :=
    CokernelCofork.mapIsColimit
      (CokernelCofork.ofπ (cokernel.π η) (cokernel.condition η))
      (cokernelIsCokernel η) Eₚ
  apply Cofork.IsColimit.hom_ext hS
  change (cokernel.π η).f p ≫ ρ.v p q hpq = (cokernel.π η).f p ≫ σ.v p q hpq
  simpa only [zero_cochain_comp_v, ofHom_v] using congr_v hρσ p q hpq

/--
Construct the raw desuspended generator by cokernel descent. The shift is minus the integer
cochain degree, with shift signs.
-/
noncomputable def cokernelShiftGenerator (η : U ⟶ C) (d : ℤ)
    (τ : Cochain C A d)
    (hpre : (ofHom η).comp τ (zero_add d) = 0) :
    let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
    Cochain ((cokernel η)⟦-d⟧) A 0 := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  let ρ : Cochain (cokernel η) A d :=
    Cochain.mk fun p q hpq => by
      let Eₚ := HomologicalComplex.eval D (ComplexShape.up ℤ) p
      let _ : PreservesColimit (parallelPair η 0) Eₚ :=
        HomologicalComplex.eval_preservesColimit_of_hasCokernel_f η p
      let S : CokernelCofork (η.f p) :=
        (CokernelCofork.ofπ (cokernel.π η) (cokernel.condition η)).map Eₚ
      let hS : IsColimit S :=
        CokernelCofork.mapIsColimit
          (CokernelCofork.ofπ (cokernel.π η) (cokernel.condition η))
          (cokernelIsCokernel η) Eₚ
      have hτ : η.f p ≫ τ.v p q hpq = 0 := by
        have h := congr_v hpre p q hpq
        simpa only [zero_cochain_comp_v, ofHom_v, zero_v] using h
      exact (CokernelCofork.IsColimit.desc' hS (τ.v p q hpq) hτ).1
  exact ρ.leftShift (-d) 0 (add_neg_cancel d)

/-- Unshift and precompose with the literal cokernel projection to
recover the entire original raw cochain, not only one component. -/
theorem cokernelShiftGenerator_recover (η : U ⟶ C) (d : ℤ)
    (τ : Cochain C A d)
    (hpre : (ofHom η).comp τ (zero_add d) = 0) :
    let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
    (ofHom (cokernel.π η)).comp
      ((cokernelShiftGenerator η d τ hpre).leftUnshift d (add_neg_cancel d))
      (zero_add d) = τ := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  dsimp only [cokernelShiftGenerator]
  rw [leftUnshift_leftShift]
  apply Cochain.ext
  intro p q hpq
  let Eₚ := HomologicalComplex.eval D (ComplexShape.up ℤ) p
  let _ : PreservesColimit (parallelPair η 0) Eₚ :=
    HomologicalComplex.eval_preservesColimit_of_hasCokernel_f η p
  let S : CokernelCofork (η.f p) :=
    (CokernelCofork.ofπ (cokernel.π η) (cokernel.condition η)).map Eₚ
  let hS : IsColimit S :=
    CokernelCofork.mapIsColimit
      (CokernelCofork.ofπ (cokernel.π η) (cokernel.condition η))
      (cokernelIsCokernel η) Eₚ
  have hτ : η.f p ≫ τ.v p q hpq = 0 := by
    have h := congr_v hpre p q hpq
    simpa only [zero_cochain_comp_v, ofHom_v, zero_v] using h
  rw [zero_cochain_comp_v, ofHom_v, Cochain.mk_v]
  change (cokernel.π η).f p ≫
    (CokernelCofork.IsColimit.desc' hS (τ.v p q hpq) hτ).1 = τ.v p q hpq
  exact (CokernelCofork.IsColimit.desc' hS (τ.v p q hpq) hτ).2

/-- Literal projection–unshift recovery uniquely determines the raw
generator. No component epimorphism or splitting is a new hypothesis. -/
theorem cokernelShiftGenerator_unique (η : U ⟶ C) (d : ℤ)
    (τ : Cochain C A d)
    (hpre : (ofHom η).comp τ (zero_add d) = 0) :
    let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
    ∀ γ : Cochain ((cokernel η)⟦-d⟧) A 0,
      (ofHom (cokernel.π η)).comp
          (γ.leftUnshift d (add_neg_cancel d)) (zero_add d) = τ →
        γ = cokernelShiftGenerator η d τ hpre := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  dsimp only
  intro γ hγ
  have hfactor :
      γ.leftUnshift d (add_neg_cancel d) =
        (cokernelShiftGenerator η d τ hpre).leftUnshift d (add_neg_cancel d) :=
    cokernel_precomp_injective η d
      (hγ.trans (cokernelShiftGenerator_recover η d τ hpre).symm)
  have hs := congrArg (fun z : Cochain (cokernel η) A d =>
    z.leftShift (-d) 0 (add_neg_cancel d)) hfactor
  simpa only [leftShift_leftUnshift] using hs

/-- The generator does not depend on the proof of source vanishing. -/
theorem cokernelShiftGenerator_proof_irrel (η : U ⟶ C) (d : ℤ)
    (τ : Cochain C A d)
    (h₁ h₂ : (ofHom η).comp τ (zero_add d) = 0) :
    cokernelShiftGenerator η d τ h₁ = cokernelShiftGenerator η d τ h₂ := rfl

/-- The raw zero cochain has zero generator, at every integer degree. -/
theorem cokernelShiftGenerator_zero (η : U ⟶ C) (d : ℤ) :
    cokernelShiftGenerator η d (0 : Cochain C A d)
      (Cochain.comp_zero (ofHom η) (zero_add d)) = 0 := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  symm
  apply cokernelShiftGenerator_unique η d (0 : Cochain C A d)
    (Cochain.comp_zero (ofHom η) (zero_add d))
  rw [leftUnshift_zero, Cochain.comp_zero]

omit [HasCokernels D] in
private theorem leftUnshift_comp_raw_zero {Q : CochainComplex D ℤ} (d : ℤ)
    (γ : Cochain (Q⟦-d⟧) A 0) (κ : Cochain A B 0) :
    (γ.comp κ (zero_add 0)).leftUnshift d (add_neg_cancel d) =
      (γ.leftUnshift d (add_neg_cancel d)).comp κ (add_zero d) := by
  apply (leftShiftAddEquiv Q B d (-d) 0 (add_neg_cancel d)).injective
  change ((γ.comp κ (zero_add 0)).leftUnshift d (add_neg_cancel d)).leftShift
      (-d) 0 (add_neg_cancel d) =
    ((γ.leftUnshift d (add_neg_cancel d)).comp κ (add_zero d)).leftShift
      (-d) 0 (add_neg_cancel d)
  rw [leftShift_leftUnshift, leftShift_comp_zero_cochain, leftShift_leftUnshift]

/-- The raw generator commutes with degree-zero target cochains, which
need not themselves be closed. Source vanishing of the composite is derived. -/
theorem cokernelShiftGenerator_comp (η : U ⟶ C) (d : ℤ)
    (τ : Cochain C A d)
    (hpre : (ofHom η).comp τ (zero_add d) = 0) (κ : Cochain A B 0) :
    let hpre' : (ofHom η).comp (τ.comp κ (add_zero d)) (zero_add d) = 0 := by
      rw [← Cochain.comp_assoc_of_first_is_zero_cochain, hpre, Cochain.zero_comp]
    cokernelShiftGenerator η d (τ.comp κ (add_zero d)) hpre' =
      (cokernelShiftGenerator η d τ hpre).comp κ (zero_add 0) := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  dsimp only
  symm
  apply cokernelShiftGenerator_unique η d
    (τ.comp κ (add_zero d))
    (by rw [← Cochain.comp_assoc_of_first_is_zero_cochain, hpre, Cochain.zero_comp])
  rw [leftUnshift_comp_raw_zero, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    cokernelShiftGenerator_recover]

/--
Unshifting any raw generator and precomposing with the projection gives a source-vanishing
cochain. This is the converse to raw descent.
-/
theorem cokernelShiftGenerator_reconstruction_vanish (η : U ⟶ C) (d : ℤ) :
    let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
    ∀ γ : Cochain ((cokernel η)⟦-d⟧) A 0,
      (ofHom η).comp
        ((ofHom (cokernel.π η)).comp
          (γ.leftUnshift d (add_neg_cancel d)) (zero_add d)) (zero_add d) = 0 := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  dsimp only
  intro γ
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← ofHom_comp,
    cokernel.condition, ofHom_zero, Cochain.zero_comp]

/--
Descent after literal projection–unshift reconstruction returns the original raw generator. Both
directions use the cokernel and shift.
-/
theorem cokernelShiftGenerator_of_reconstruction (η : U ⟶ C) (d : ℤ) :
    let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
    ∀ γ : Cochain ((cokernel η)⟦-d⟧) A 0,
      cokernelShiftGenerator η d
        ((ofHom (cokernel.π η)).comp
          (γ.leftUnshift d (add_neg_cancel d)) (zero_add d))
        (cokernelShiftGenerator_reconstruction_vanish η d γ) = γ := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  dsimp only
  intro γ
  symm
  exact cokernelShiftGenerator_unique η d
    ((ofHom (cokernel.π η)).comp
      (γ.leftUnshift d (add_neg_cancel d)) (zero_add d))
    (cokernelShiftGenerator_reconstruction_vanish η d γ) γ rfl

/-- Addition of source-vanishing raw cochains gives addition of generators,
in every integer degree. The source vanishing of the sum is derived. -/
theorem cokernelShiftGenerator_add (η : U ⟶ C) (d : ℤ)
    (τ₁ τ₂ : Cochain C A d)
    (h₁ : (ofHom η).comp τ₁ (zero_add d) = 0)
    (h₂ : (ofHom η).comp τ₂ (zero_add d) = 0) :
    let hsum : (ofHom η).comp (τ₁ + τ₂) (zero_add d) = 0 := by
      rw [Cochain.comp_add, h₁, h₂, add_zero]
    cokernelShiftGenerator η d (τ₁ + τ₂) hsum =
      cokernelShiftGenerator η d τ₁ h₁ + cokernelShiftGenerator η d τ₂ h₂ := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  dsimp only
  symm
  apply cokernelShiftGenerator_unique η d (τ₁ + τ₂)
    (by rw [Cochain.comp_add, h₁, h₂, add_zero])
  rw [leftUnshift_add, Cochain.comp_add,
    cokernelShiftGenerator_recover, cokernelShiftGenerator_recover]

/--
The raw generator of a negative cochain is the negative generator, with source vanishing proved by
additive composition.
-/
theorem cokernelShiftGenerator_neg (η : U ⟶ C) (d : ℤ)
    (τ : Cochain C A d) (hpre : (ofHom η).comp τ (zero_add d) = 0) :
    let hneg : (ofHom η).comp (-τ) (zero_add d) = 0 := by
      rw [Cochain.comp_neg, hpre, neg_zero]
    cokernelShiftGenerator η d (-τ) hneg = -cokernelShiftGenerator η d τ hpre := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  dsimp only
  symm
  apply cokernelShiftGenerator_unique η d (-τ)
    (by rw [Cochain.comp_neg, hpre, neg_zero])
  rw [leftUnshift_neg, Cochain.comp_neg, cokernelShiftGenerator_recover]

omit [HasCokernels D] in
private theorem leftShift_precomp_raw_zero
    {Q' Q : CochainComplex D ℤ} (c : Q' ⟶ Q) (d : ℤ)
    (ρ : Cochain Q A d) :
    ((ofHom c).comp ρ (zero_add d)).leftShift (-d) 0 (add_neg_cancel d) =
      (ofHom (c⟦-d⟧')).comp
        (ρ.leftShift (-d) 0 (add_neg_cancel d)) (zero_add 0) := by
  apply Cochain.ext₀
  intro p
  have hpd : p + -d + d = p := by rw [add_assoc, neg_add_cancel, add_zero]
  let s : ℤˣ := ((-d) * 0 + ((-d) * (-d - 1)) / 2).negOnePow
  have hleftComp :
      (Q'.shiftFunctorObjXIso (-d) p (p + -d) rfl).hom ≫
          ((ofHom c).comp ρ (zero_add d)).v (p + -d) p hpd =
        c.f (p + -d) ≫ ρ.v (p + -d) p hpd := by
    calc
      _ = ((ofHom c).comp ρ (zero_add d)).v (p + -d) p hpd := by
        change (𝟙 (Q'.X (p + -d))) ≫
            ((ofHom c).comp ρ (zero_add d)).v (p + -d) p hpd =
          ((ofHom c).comp ρ (zero_add d)).v (p + -d) p hpd
        exact Category.id_comp _
      _ = c.f (p + -d) ≫ ρ.v (p + -d) p hpd := by
        simpa only [ofHom_v] using
          (zero_cochain_comp_v (ofHom c) ρ (p + -d) p hpd)
  have hleft :
      (((ofHom c).comp ρ (zero_add d)).leftShift (-d) 0 (add_neg_cancel d)).v
        p p (add_zero p) = s • (c.f (p + -d) ≫ ρ.v (p + -d) p hpd) := by
    calc
      _ = s • ((Q'.shiftFunctorObjXIso (-d) p (p + -d) rfl).hom ≫
          ((ofHom c).comp ρ (zero_add d)).v (p + -d) p hpd) :=
        leftShift_v ((ofHom c).comp ρ (zero_add d)) (-d) 0 (add_neg_cancel d)
          p p (add_zero p) (p + -d) hpd
      _ = s • (c.f (p + -d) ≫ ρ.v (p + -d) p hpd) :=
        congrArg (fun z : Q'.X (p + -d) ⟶ A.X p => s • z) hleftComp
  have hρComp : (Q.shiftFunctorObjXIso (-d) p (p + -d) rfl).hom ≫
      ρ.v (p + -d) p hpd = ρ.v (p + -d) p hpd := by
    change (𝟙 (Q.X (p + -d))) ≫ ρ.v (p + -d) p hpd = ρ.v (p + -d) p hpd
    exact Category.id_comp _
  have hρ : (ρ.leftShift (-d) 0 (add_neg_cancel d)).v p p (add_zero p) =
      s • ρ.v (p + -d) p hpd := by
    calc
      _ = s • ((Q.shiftFunctorObjXIso (-d) p (p + -d) rfl).hom ≫
          ρ.v (p + -d) p hpd) :=
        leftShift_v ρ (-d) 0 (add_neg_cancel d) p p (add_zero p) (p + -d) hpd
      _ = s • ρ.v (p + -d) p hpd :=
        congrArg (fun z : Q.X (p + -d) ⟶ A.X p => s • z) hρComp
  have hright :
      ((ofHom (c⟦-d⟧')).comp (ρ.leftShift (-d) 0 (add_neg_cancel d)) (zero_add 0)).v
        p p (add_zero p) = s • (c.f (p + -d) ≫ ρ.v (p + -d) p hpd) := by
    calc
      _ = (c⟦-d⟧').f p ≫ (ρ.leftShift (-d) 0 (add_neg_cancel d)).v
          p p (add_zero p) := by
        simpa only [ofHom_v] using
          (zero_cochain_comp_v (ofHom (c⟦-d⟧'))
            (ρ.leftShift (-d) 0 (add_neg_cancel d)) p p (add_zero p))
      _ = (c⟦-d⟧').f p ≫ (s • ρ.v (p + -d) p hpd) :=
        congrArg (fun z => (c⟦-d⟧').f p ≫ z) hρ
      _ = s • (c.f (p + -d) ≫ ρ.v (p + -d) p hpd) := by
        rw [CochainComplex.shiftFunctor_map_f', Linear.comp_units_smul]
  exact hleft.trans hright.symm

omit [HasCokernels D] in
private theorem leftUnshift_precomp_raw_zero
    {Q' Q : CochainComplex D ℤ} (c : Q' ⟶ Q) (d : ℤ)
    (γ : Cochain (Q⟦-d⟧) A 0) :
    ((ofHom (c⟦-d⟧')).comp γ (zero_add 0)).leftUnshift d (add_neg_cancel d) =
      (ofHom c).comp (γ.leftUnshift d (add_neg_cancel d)) (zero_add d) := by
  apply (leftShiftAddEquiv Q' A d (-d) 0 (add_neg_cancel d)).injective
  change (((ofHom (c⟦-d⟧')).comp γ (zero_add 0)).leftUnshift
      d (add_neg_cancel d)).leftShift (-d) 0 (add_neg_cancel d) =
    ((ofHom c).comp (γ.leftUnshift d (add_neg_cancel d)) (zero_add d)).leftShift
      (-d) 0 (add_neg_cancel d)
  rw [leftShift_leftUnshift, leftShift_precomp_raw_zero, leftShift_leftUnshift]

/--
A commuting square of complex maps transports the raw generator by the shifted cokernel map. No
square map is assumed invertible.
-/
theorem cokernelShiftGenerator_precomp
    {U' C' : CochainComplex D ℤ} (η : U ⟶ C) (η' : U' ⟶ C')
    (a : U' ⟶ U) (c : C' ⟶ C) (hsquare : η' ≫ c = a ≫ η)
    (d : ℤ) (τ : Cochain C A d)
    (hpre : (ofHom η).comp τ (zero_add d) = 0) :
    let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
    let _ : HasCokernel η' := HomologicalComplex.hasCokernel_of_hasCokernel_f η'
    let hpre' : (ofHom η').comp ((ofHom c).comp τ (zero_add d)) (zero_add d) = 0 := by
      rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← ofHom_comp, hsquare,
        ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain, hpre, Cochain.comp_zero]
    cokernelShiftGenerator η' d ((ofHom c).comp τ (zero_add d)) hpre' =
      (ofHom ((cokernel.map η' η a c hsquare)⟦-d⟧')).comp
        (cokernelShiftGenerator η d τ hpre) (zero_add 0) := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  let _ : HasCokernel η' := HomologicalComplex.hasCokernel_of_hasCokernel_f η'
  dsimp only
  have hq : cokernel.π η' ≫ cokernel.map η' η a c hsquare = c ≫ cokernel.π η :=
    cokernel.π_desc _ _ _
  symm
  apply cokernelShiftGenerator_unique η' d ((ofHom c).comp τ (zero_add d))
    (by
      rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← ofHom_comp, hsquare,
        ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain, hpre, Cochain.comp_zero])
  rw [leftUnshift_precomp_raw_zero, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← ofHom_comp, hq, ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    cokernelShiftGenerator_recover]

/--
Whole recovery commutes with the internal Hom differential with the left-shift sign, including
nonadjacent and negative integer degrees.
-/
theorem cokernelShiftGenerator_δ_recover (η : U ⟶ C) (d : ℤ)
    (τ : Cochain C A d) (hpre : (ofHom η).comp τ (zero_add d) = 0) (m : ℤ) :
    let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
    δ d m τ = (-d).negOnePow •
      (ofHom (cokernel.π η)).comp
        ((δ 0 (m - d) (cokernelShiftGenerator η d τ hpre)).leftUnshift
          m (sub_eq_add_neg m d).symm) (zero_add m) := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  have h := congrArg (δ d m) (cokernelShiftGenerator_recover η d τ hpre)
  rw [δ_ofHom_comp,
    δ_leftUnshift _ d (add_neg_cancel d) m (m - d) (sub_eq_add_neg m d).symm,
    comp_units_smul] at h
  exact h.symm

/-- At degree one the internal differential recovery has a minus sign.
This equation imposes no closedness and no total-Cobar compatibility. -/
theorem cokernelShiftGenerator_δ_degree_one (η : U ⟶ C)
    (τ : Cochain C A 1) (hpre : (ofHom η).comp τ (zero_add 1) = 0) :
    let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
    δ 1 2 τ = -((ofHom (cokernel.π η)).comp
      ((δ 0 1 (cokernelShiftGenerator η 1 τ hpre)).leftUnshift 2
        (show (2 : ℤ) + -1 = 1 by decide)) (zero_add 2)) := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  have h := congrArg (δ 1 2) (cokernelShiftGenerator_recover η 1 τ hpre)
  rw [δ_ofHom_comp,
    δ_leftUnshift _ 1 (add_neg_cancel 1) 2 1
      (show (2 : ℤ) + -1 = 1 by decide), comp_units_smul] at h
  simpa only [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul] using h.symm

/--
Literal component recovery with the shift-component isomorphism and its integer sign. The full raw
generator is characterized by recovery.
-/
theorem cokernelShiftGenerator_recover_v (η : U ⟶ C) (d : ℤ)
    (τ : Cochain C A d) (hpre : (ofHom η).comp τ (zero_add d) = 0)
    (p q : ℤ) (hpq : p + d = q) :
    let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
    τ.v p q hpq = (((-d) * (-d - 1)) / 2).negOnePow •
      ((cokernel.π η).f p ≫
        ((cokernel η).shiftFunctorObjXIso (-d) q p
          (by rw [← hpq, add_assoc, add_neg_cancel, add_zero])).inv ≫
        (cokernelShiftGenerator η d τ hpre).v q q (add_zero q)) := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  have h := congr_v (cokernelShiftGenerator_recover η d τ hpre) p q hpq
  rw [zero_cochain_comp_v, ofHom_v,
    leftUnshift_v _ d (add_neg_cancel d) p q hpq q (add_zero q),
    Linear.comp_units_smul] at h
  simpa only [mul_zero, zero_add, Category.assoc] using h.symm

/-- The degree-one generator has the literal negative inverse-unshift
formula at every integer component, including negative source degrees. -/
theorem cokernelShiftGenerator_recover_v_degree_one (η : U ⟶ C)
    (τ : Cochain C A 1) (hpre : (ofHom η).comp τ (zero_add 1) = 0) (p : ℤ) :
    let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
    τ.v p (p + 1) rfl = -((cokernel.π η).f p ≫
      ((cokernel η).shiftFunctorObjXIso (-1) (p + 1) p
        (by rw [add_assoc, add_neg_cancel, add_zero])).inv ≫
      (cokernelShiftGenerator η 1 τ hpre).v (p + 1) (p + 1) (add_zero (p + 1))) := by
  let _ : HasCokernel η := HomologicalComplex.hasCokernel_of_hasCokernel_f η
  have h := cokernelShiftGenerator_recover_v η 1 τ hpre p (p + 1) rfl
  have hs : (((-(1 : ℤ)) * (-(1 : ℤ) - 1)) / 2) = 1 := by decide
  simpa only [hs, Int.negOnePow_one, Units.neg_smul, one_smul] using h

end CochainComplex.HomComplex.Cochain
