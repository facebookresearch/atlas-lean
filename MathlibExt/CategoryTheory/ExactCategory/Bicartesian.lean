/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.ExactCategory.PushoutFlag
public import MathlibExt.CategoryTheory.ExactCategory.MorphismProperty
public import Mathlib.Algebra.Homology.CommSq

/-!
# Bicartesian squares in exact categories

Let `C` be an additive category with a chosen Quillen exact structure.
A morphism between admissible exact short complexes that is invertible on
the left gives a pullback square on the last two objects; invertibility
on the right gives a pushout square on the first two objects. The associated
biproduct kernel–cokernel sequences characterize these squares.

References: Theo Bühler, *Exact Categories*, Proposition 2.12,
Proposition 3.1, and Corollary 3.2.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.ExactCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- In an additive exact category `C`, let `sq` be a commutative square
`X₁ → X₂`, `X₁ → X₃`, with target `X₄`. If its associated biproduct
short complex is admissible exact, the original square is a pushout. -/
theorem isPushout_of_isAdmissibleExact_shortComplex
    {X₁ X₂ X₃ X₄ : C}
    {f : X₁ ⟶ X₂} {g : X₁ ⟶ X₃}
    {inl : X₂ ⟶ X₄} {inr : X₃ ⟶ X₄}
    (sq : CommSq f g inl inr)
    (h : IsAdmissibleExact sq.shortComplex) :
    IsPushout f g inl inr := by
  have hc : IsColimit sq.cokernelCofork :=
    isColimit_cokernelCofork_of_isAdmissibleExact h
  exact IsPushout.of_isColimit' sq
    (sq.isColimitEquivIsColimitCokernelCofork.symm hc)

/-- In an additive exact category `C`, let `sq` be a commutative square
with initial object `X₁` and final object `X₄`. If the associated
biproduct short complex with map into `X₂ ⊞ X₃` is admissible exact,
the original square is a pullback. -/
theorem isPullback_of_isAdmissibleExact_shortComplex'
    {X₁ X₂ X₃ X₄ : C}
    {fst : X₁ ⟶ X₂} {snd : X₁ ⟶ X₃}
    {f : X₂ ⟶ X₄} {g : X₃ ⟶ X₄}
    (sq : CommSq fst snd f g)
    (h : IsAdmissibleExact sq.shortComplex') :
    IsPullback fst snd f g := by
  have hk : IsLimit sq.kernelFork := by
    exact IsLimit.ofIsoLimit
      (isLimit_kernelFork_of_isAdmissibleExact h)
      (Cone.ext (Iso.refl _) (by
        rintro (_ | _) <;>
          simp [CommSq.shortComplex', CommSq.kernelFork]))
  exact IsPullback.of_isLimit' sq
    (sq.isLimitEquivIsLimitKernelFork.symm hk)

private def negIdIso (X : C) : X ≅ X where
  hom := -𝟙 X
  inv := -𝟙 X
  hom_inv_id := by simp
  inv_hom_id := by simp

private theorem isPullback_g_of_common_left
    {A B X B' X' : C}
    (i : A ⟶ B) (p : B ⟶ X)
    (j : A ⟶ B') (q : B' ⟶ X')
    (b : B ⟶ B') (c : X ⟶ X')
    (wi : i ≫ p = 0) (wj : j ≫ q = 0)
    (hS : IsAdmissibleExact (ShortComplex.mk i p wi))
    (hT : IsAdmissibleExact (ShortComplex.mk j q wj))
    (hLeft : i ≫ b = j) (hRight : p ≫ c = b ≫ q) :
    IsPullback p b c q := by
  let wjNeg : (-j) ≫ q = 0 := by simp [wj]
  let Tneg : ShortComplex C := ShortComplex.mk (-j) q wjNeg
  have hTneg : IsAdmissibleExact Tneg := by
    let T : ShortComplex C := ShortComplex.mk j q wj
    have hT' : IsAdmissibleExact T := by
      simpa only [T] using hT
    have e : T ≅ Tneg :=
      ShortComplex.isoMk (negIdIso A) (Iso.refl B') (Iso.refl X')
        (by simp [T, Tneg, negIdIso])
        (by simp [T, Tneg])
    exact isAdmissibleExact_of_iso e hT'
  obtain ⟨P, x, y, sq, _hx⟩ :=
    admissibleMono_pushout
      (X := A) (Y := B') (i := -j) (isAdmissibleMono_f hTneg)
      (X' := B) (f := i)
  let m : P ⟶ X' := pushoutQuotientMap i (-j) q x y wjNeg sq
  have wm : x ≫ m = 0 := by
    exact pushoutQuotientMap_x i (-j) q x y wjNeg sq
  have hym : y ≫ m = q := by
    exact pushoutQuotientMap_y i (-j) q x y wjNeg sq
  have hP : IsAdmissibleExact (ShortComplex.mk x m wm) := by
    simpa only [m, wm] using
      isAdmissibleExact_pushoutQuotientMap i (-j) q x y wjNeg hTneg sq
  let dx : B ⟶ X ⊞ B' := biprod.lift p b
  let dy : B' ⟶ X ⊞ B' := -biprod.inr
  have hxy : i ≫ dx = (-j) ≫ dy := by
    apply biprod.hom_ext
    · simp [dx, dy, wi]
    · simp [dx, dy, hLeft]
  let d : P ⟶ X ⊞ B' := sq.desc dx dy hxy
  have hxd : x ≫ d = dx := by
    exact sq.inl_desc dx dy hxy
  have hyd : y ≫ d = dy := by
    exact sq.inr_desc dx dy hxy
  let hcS := isColimit_cokernelCofork_of_isAdmissibleExact hS
  have hz0 : i ≫ (x + b ≫ y) = 0 := by
    rw [Preadditive.comp_add, ← Category.assoc, sq.w, hLeft]
    simp
  let z : X ⟶ P :=
    hcS.desc (CokernelCofork.ofπ (x + b ≫ y) hz0)
  have hpz : p ≫ z = x + b ≫ y := by
    change p ≫ hcS.desc (CokernelCofork.ofπ (x + b ≫ y) hz0) = _
    exact Cofork.IsColimit.π_desc hcS
  let dInv : X ⊞ B' ⟶ P := biprod.desc z (-y)
  have hd_dInv : d ≫ dInv = 𝟙 P := by
    apply sq.hom_ext
    · calc
        x ≫ (d ≫ dInv) = (x ≫ d) ≫ dInv := by
          rw [Category.assoc]
        _ = dx ≫ dInv := by rw [hxd]
        _ = x := by simp [dx, dInv, hpz, add_assoc]
        _ = x ≫ 𝟙 P := by simp
    · calc
        y ≫ (d ≫ dInv) = (y ≫ d) ≫ dInv := by
          rw [Category.assoc]
        _ = dy ≫ dInv := by rw [hyd]
        _ = y := by simp [dy, dInv]
        _ = y ≫ 𝟙 P := by simp
  let _ : Epi p := (isAdmissibleEpi_g hS).epi
  have hzd : z ≫ d = biprod.inl := by
    rw [← cancel_epi p]
    calc
      p ≫ (z ≫ d) = (p ≫ z) ≫ d := by rw [Category.assoc]
      _ = (x + b ≫ y) ≫ d := by rw [hpz]
      _ = x ≫ d + (b ≫ y) ≫ d := by
        rw [Preadditive.add_comp]
      _ = dx + b ≫ dy := by rw [hxd, Category.assoc, hyd]
      _ = p ≫ biprod.inl := by
        simp [dx, dy, biprod.lift_eq, add_assoc]
  have hdInv_d : dInv ≫ d = 𝟙 (X ⊞ B') := by
    apply biprod.hom_ext'
    · simp [dInv, hzd]
    · simp [dInv, hyd, dy]
  let dIso : P ≅ X ⊞ B' :=
    { hom := d
      inv := dInv
      hom_inv_id := hd_dInv
      inv_hom_id := hdInv_d }
  let kg : X ⊞ B' ⟶ X' := biprod.desc c (-q)
  have hdkg : d ≫ kg = m := by
    apply sq.hom_ext
    · calc
        x ≫ (d ≫ kg) = (x ≫ d) ≫ kg := by
          rw [Category.assoc]
        _ = dx ≫ kg := by rw [hxd]
        _ = 0 := by simp [dx, kg, hRight]
        _ = x ≫ m := wm.symm
    · calc
        y ≫ (d ≫ kg) = (y ≫ d) ≫ kg := by
          rw [Category.assoc]
        _ = dy ≫ kg := by rw [hyd]
        _ = q := by simp [dy, kg]
        _ = y ≫ m := hym.symm
  let rightSq : CommSq p b c q := ⟨hRight⟩
  let K : ShortComplex C := rightSq.shortComplex'
  have rowIso : ShortComplex.mk x m wm ≅ K :=
    ShortComplex.isoMk (Iso.refl B) dIso (Iso.refl X')
      (by
        change (𝟙 B) ≫ biprod.lift p b = x ≫ d
        rw [Category.id_comp]
        simpa only [dx] using hxd.symm)
      (by
        change d ≫ biprod.desc c (-q) = m ≫ 𝟙 X'
        rw [Category.comp_id]
        simpa only [kg] using hdkg)
  have hK : IsAdmissibleExact K :=
    isAdmissibleExact_of_iso rowIso hP
  exact isPullback_of_isAdmissibleExact_shortComplex' rightSq hK

/-- In an additive exact category `C`, let `φ : S → T` be a morphism of
admissible exact short complexes. If its left component `φ₁` is an
isomorphism, the square formed by `S.g`, `T.g`, `φ₂`, and `φ₃` is a pullback. -/
theorem isPullback_g_of_isAdmissibleExact_of_isIso_left
    {S T : ShortComplex C} (φ : S ⟶ T)
    (hS : IsAdmissibleExact S) (hT : IsAdmissibleExact T)
    [IsIso φ.τ₁] :
    IsPullback S.g φ.τ₂ φ.τ₃ T.g := by
  let wSbar : (inv φ.τ₁ ≫ S.f) ≫ S.g = 0 := by
    rw [Category.assoc, S.zero, comp_zero]
  let Sbar : ShortComplex C :=
    ShortComplex.mk (inv φ.τ₁ ≫ S.f) S.g wSbar
  have hSbar : IsAdmissibleExact Sbar := by
    have e : S ≅ Sbar :=
      ShortComplex.isoMk (asIso φ.τ₁) (Iso.refl S.X₂) (Iso.refl S.X₃)
        (by simp [Sbar]) (by simp [Sbar])
    exact isAdmissibleExact_of_iso e hS
  have hLeft : (inv φ.τ₁ ≫ S.f) ≫ φ.τ₂ = T.f := by
    calc
      (inv φ.τ₁ ≫ S.f) ≫ φ.τ₂ =
          inv φ.τ₁ ≫ (S.f ≫ φ.τ₂) := Category.assoc _ _ _
      _ = inv φ.τ₁ ≫ (φ.τ₁ ≫ T.f) := by rw [← φ.comm₁₂]
      _ = T.f := by simp
  exact isPullback_g_of_common_left
    (inv φ.τ₁ ≫ S.f) S.g T.f T.g φ.τ₂ φ.τ₃
    wSbar T.zero hSbar hT hLeft φ.comm₂₃.symm

/-- In an additive exact category `C`, let `φ : S → T` be a morphism of
admissible exact short complexes. If `φ₁` is an isomorphism and `φ₃`
is an admissible monomorphism, the middle component `φ₂` is an admissible
monomorphism. -/
theorem isAdmissibleMono_middle_of_isIso_left
    {S T : ShortComplex C} (φ : S ⟶ T)
    (hS : IsAdmissibleExact S) (hT : IsAdmissibleExact T)
    [IsIso φ.τ₁] (h₃ : IsAdmissibleMono φ.τ₃) :
    IsAdmissibleMono φ.τ₂ :=
  isAdmissibleMono_of_isPullback
    (isPullback_g_of_isAdmissibleExact_of_isIso_left φ hS hT)
    h₃ (isAdmissibleEpi_g hT)

private theorem isPushout_f_of_common_right
    {X B A X' B' : C}
    (i : X ⟶ B) (p : B ⟶ A)
    (j : X' ⟶ B') (q : B' ⟶ A)
    (a : X ⟶ X') (b : B ⟶ B')
    (wi : i ≫ p = 0) (wj : j ≫ q = 0)
    (hS : IsAdmissibleExact (ShortComplex.mk i p wi))
    (hT : IsAdmissibleExact (ShortComplex.mk j q wj))
    (hLeft : i ≫ b = a ≫ j) (hRight : b ≫ q = p) :
    IsPushout i a b j := by
  let wiNeg : i ≫ (-p) = 0 := by simp [wi]
  let Sneg : ShortComplex C := ShortComplex.mk i (-p) wiNeg
  have hSneg : IsAdmissibleExact Sneg := by
    let S : ShortComplex C := ShortComplex.mk i p wi
    have hS' : IsAdmissibleExact S := by
      simpa only [S] using hS
    have e : S ≅ Sneg :=
      ShortComplex.isoMk (Iso.refl X) (Iso.refl B) (negIdIso A)
        (by simp [S, Sneg])
        (by simp [S, Sneg, negIdIso])
    exact isAdmissibleExact_of_iso e hS'
  obtain ⟨P, x, y, sq, hx⟩ :=
    admissibleEpi_pullback
      (Y := B) (Z := A) (p := -p) (isAdmissibleEpi_g hSneg)
      (Z' := B') (g := q)
  let m : X ⟶ P := sq.lift (0 : X ⟶ B') i (by simp [wi])
  have hmx : m ≫ x = 0 := by
    exact sq.lift_fst _ _ _
  have hmy : m ≫ y = i := by
    exact sq.lift_snd _ _ _
  let hkS := isLimit_kernelFork_of_isAdmissibleExact hSneg
  let u {W : C} (g : W ⟶ P) (hg : g ≫ x = 0) : W ⟶ X :=
    hkS.lift (KernelFork.ofι (g ≫ y) (by
      calc
        (g ≫ y) ≫ (-p) = g ≫ (y ≫ (-p)) := Category.assoc _ _ _
        _ = g ≫ (x ≫ q) := by rw [← sq.w]
        _ = (g ≫ x) ≫ q := (Category.assoc _ _ _).symm
        _ = 0 := by rw [hg, zero_comp]))
  have hu {W : C} (g : W ⟶ P) (hg : g ≫ x = 0) :
      u g hg ≫ i = g ≫ y := by
    exact hkS.fac (KernelFork.ofι (g ≫ y) _) WalkingParallelPair.zero
  have hum {W : C} (g : W ⟶ P) (hg : g ≫ x = 0) :
      u g hg ≫ m = g := by
    apply sq.hom_ext
    · calc
        (u g hg ≫ m) ≫ x = u g hg ≫ (m ≫ x) := Category.assoc _ _ _
        _ = 0 := by rw [hmx, comp_zero]
        _ = g ≫ x := hg.symm
    · calc
        (u g hg ≫ m) ≫ y = u g hg ≫ (m ≫ y) := Category.assoc _ _ _
        _ = u g hg ≫ i := by rw [hmy]
        _ = g ≫ y := hu g hg
  have hKernelM : IsLimit (KernelFork.ofι m hmx) := by
    let _ : Mono i := (isAdmissibleMono_f hSneg).mono
    refine KernelFork.IsLimit.ofι m hmx (fun g hg => u g hg) ?_ ?_
    · intro W g hg
      exact hum g hg
    · intro W g hg l hl
      apply (cancel_mono i).mp
      calc
        l ≫ i = l ≫ (m ≫ y) := by rw [hmy]
        _ = (l ≫ m) ≫ y := (Category.assoc _ _ _).symm
        _ = g ≫ y := by rw [hl]
        _ = u g hg ≫ i := (hu g hg).symm
  have hP : IsAdmissibleExact (ShortComplex.mk m x hmx) := by
    obtain ⟨K, k, wk, hK⟩ := hx
    let hKernelK := isLimit_kernelFork_of_isAdmissibleExact hK
    let e : K ≅ X := hKernelK.conePointUniqueUpToIso hKernelM
    have he : e.hom ≫ m = k := by
      have h := IsLimit.conePointUniqueUpToIso_hom_comp
        hKernelK hKernelM WalkingParallelPair.zero
      simpa [KernelFork.ofι] using h
    let eShort : ShortComplex.mk k x wk ≅ ShortComplex.mk m x hmx :=
      ShortComplex.isoMk e (Iso.refl P) (Iso.refl B')
        (by simpa using he) (by simp)
    exact isAdmissibleExact_of_iso eShort hK
  let dx : B ⊞ X' ⟶ B' := -biprod.desc b j
  let dy : B ⊞ X' ⟶ B := biprod.fst
  have hxy : dx ≫ q = dy ≫ (-p) := by
    apply biprod.hom_ext'
    · simp [dx, dy, hRight]
    · simp [dx, dy, wj]
  let d : B ⊞ X' ⟶ P := sq.lift dx dy hxy
  have hdx : d ≫ x = dx := by
    exact sq.lift_fst _ _ _
  have hdy : d ≫ y = dy := by
    exact sq.lift_snd _ _ _
  let hkT := isLimit_kernelFork_of_isAdmissibleExact hT
  have hz0 : (-x - y ≫ b) ≫ q = 0 := by
    rw [Preadditive.sub_comp, Preadditive.neg_comp, Category.assoc,
      hRight, sq.w]
    simp
  let z : P ⟶ X' :=
    hkT.lift (KernelFork.ofι (-x - y ≫ b) hz0)
  have hzj : z ≫ j = -x - y ≫ b := by
    exact hkT.fac (KernelFork.ofι (-x - y ≫ b) hz0)
      WalkingParallelPair.zero
  let dInv : P ⟶ B ⊞ X' := biprod.lift y z
  have hdInv_d : dInv ≫ d = 𝟙 P := by
    apply sq.hom_ext
    · calc
        (dInv ≫ d) ≫ x = dInv ≫ (d ≫ x) := Category.assoc _ _ _
        _ = dInv ≫ dx := by rw [hdx]
        _ = x := by simp [dInv, dx, hzj]
        _ = (𝟙 P) ≫ x := by simp
    · calc
        (dInv ≫ d) ≫ y = dInv ≫ (d ≫ y) := Category.assoc _ _ _
        _ = dInv ≫ dy := by rw [hdy]
        _ = y := by simp [dInv, dy]
        _ = (𝟙 P) ≫ y := by simp
  let _ : Mono j := (isAdmissibleMono_f hT).mono
  have hdz : d ≫ z = biprod.snd := by
    rw [← cancel_mono j]
    calc
      (d ≫ z) ≫ j = d ≫ (z ≫ j) := Category.assoc _ _ _
      _ = d ≫ (-x - y ≫ b) := by rw [hzj]
      _ = -(d ≫ x) - (d ≫ y) ≫ b := by simp [Preadditive.comp_sub]
      _ = -dx - dy ≫ b := by rw [hdx, hdy]
      _ = biprod.snd ≫ j := by
        dsimp only [dx, dy]
        apply biprod.hom_ext' <;> simp
  have hd_dInv : d ≫ dInv = 𝟙 (B ⊞ X') := by
    apply biprod.hom_ext
    · simp [dInv, hdy, dy]
    · simp [dInv, hdz]
  let dIso : B ⊞ X' ≅ P :=
    { hom := d
      inv := dInv
      hom_inv_id := hd_dInv
      inv_hom_id := hdInv_d }
  have hfd : biprod.lift i (-a) ≫ d = m := by
    apply sq.hom_ext
    · calc
        (biprod.lift i (-a) ≫ d) ≫ x =
            biprod.lift i (-a) ≫ (d ≫ x) := Category.assoc _ _ _
        _ = biprod.lift i (-a) ≫ dx := by rw [hdx]
        _ = 0 := by simp [dx, hLeft]
        _ = m ≫ x := hmx.symm
    · calc
        (biprod.lift i (-a) ≫ d) ≫ y =
            biprod.lift i (-a) ≫ (d ≫ y) := Category.assoc _ _ _
        _ = biprod.lift i (-a) ≫ dy := by rw [hdy]
        _ = i := by simp [dy]
        _ = m ≫ y := hmy.symm
  let leftSq : CommSq i a b j := ⟨hLeft⟩
  let K : ShortComplex C := leftSq.shortComplex
  have rowIso : K ≅ ShortComplex.mk m x hmx :=
    ShortComplex.isoMk (Iso.refl X) dIso (negIdIso B')
      (by
        change (𝟙 X) ≫ m = biprod.lift i (-a) ≫ d
        rw [Category.id_comp]
        exact hfd.symm)
      (by
        change d ≫ x = biprod.desc b j ≫ (-𝟙 B')
        rw [hdx]
        simp [dx])
  have hK : IsAdmissibleExact K :=
    isAdmissibleExact_of_iso rowIso.symm hP
  exact isPushout_of_isAdmissibleExact_shortComplex leftSq hK

/-- In an additive exact category `C`, let `φ : S → T` be a morphism of
admissible exact short complexes. If its right component `φ₃` is an
isomorphism, the square formed by `S.f`, `T.f`, `φ₁`, and `φ₂` is a pushout. -/
theorem isPushout_f_of_isAdmissibleExact_of_isIso_right
    {S T : ShortComplex C} (φ : S ⟶ T)
    (hS : IsAdmissibleExact S) (hT : IsAdmissibleExact T)
    [IsIso φ.τ₃] :
    IsPushout S.f φ.τ₁ φ.τ₂ T.f := by
  let wTbar : T.f ≫ (T.g ≫ inv φ.τ₃) = 0 := by
    rw [← Category.assoc, T.zero, zero_comp]
  let Tbar : ShortComplex C :=
    ShortComplex.mk T.f (T.g ≫ inv φ.τ₃) wTbar
  have hTbar : IsAdmissibleExact Tbar := by
    have e : T ≅ Tbar :=
      ShortComplex.isoMk (Iso.refl T.X₁) (Iso.refl T.X₂)
        (asIso φ.τ₃).symm (by simp [Tbar]) (by simp [Tbar])
    exact isAdmissibleExact_of_iso e hT
  have hRight : φ.τ₂ ≫ (T.g ≫ inv φ.τ₃) = S.g := by
    calc
      φ.τ₂ ≫ (T.g ≫ inv φ.τ₃) =
          (φ.τ₂ ≫ T.g) ≫ inv φ.τ₃ := (Category.assoc _ _ _).symm
      _ = (S.g ≫ φ.τ₃) ≫ inv φ.τ₃ := by rw [φ.comm₂₃]
      _ = S.g := by simp
  exact isPushout_f_of_common_right
    S.f S.g T.f (T.g ≫ inv φ.τ₃) φ.τ₁ φ.τ₂
    S.zero wTbar hS hTbar φ.comm₁₂.symm hRight

end CategoryTheory.ExactCategory

end
