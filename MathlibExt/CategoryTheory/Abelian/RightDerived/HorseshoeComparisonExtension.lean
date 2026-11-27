/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Authors: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Abelian.RightDerived.HorseshoePrecomposition

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
universe u v
namespace CategoryTheory.Functor.RightDerived
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]

omit [HasInjectiveResolutions C] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Let `C` be abelian, `H,K` compatible injective horseshoe data
for short exact sequences `S,T`, and `α : S → T`. Fix maps of
endpoint injective resolutions `u : H₁ → K₁` over `α₁` and
`w : H₃ → K₃` over `α₃`. There is a middle map `b⁰ : H₂⁰ → K₂⁰` commuting with both
endpoint maps and satisfying the coaugmentation equation
`ι_H₂⁰ ≫ b⁰ = α₂ ≫ ι_K₂⁰`. -/
theorem HorseshoeData.nonempty_middle_zero_comparison
    {S T : ShortComplex C} {hS : S.ShortExact} {hT : T.ShortExact}
    (H : HorseshoeData S hS) (K : HorseshoeData T hT) (α : S ⟶ T)
    (u : InjectiveResolution.Hom H.res₁ K.res₁ α.τ₁)
    (w : InjectiveResolution.Hom H.res₃ K.res₃ α.τ₃) :
    ∃ b : H.res₂.cocomplex.X 0 ⟶ K.res₂.cocomplex.X 0,
      H.φf.f 0 ≫ b = u.hom.f 0 ≫ K.φf.f 0 ∧
      b ≫ K.φg.f 0 = H.φg.f 0 ≫ w.hom.f 0 ∧
      H.res₂.ι.f 0 ≫ b = α.τ₂ ≫ K.res₂.ι.f 0 := by
  let s : (ShortComplex.mk (H.φf.f 0) (H.φg.f 0)
      (by simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
        using HomologicalComplex.congr_hom H.w 0)).Splitting := H.split 0
  let t : (ShortComplex.mk (K.φf.f 0) (K.φg.f 0)
      (by simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
        using HomologicalComplex.congr_hom K.w 0)).Splitting := K.split 0
  let u0 := u.hom.f 0
  let w0 := w.hom.f 0
  let b0 : H.res₂.cocomplex.X 0 ⟶ K.res₂.cocomplex.X 0 := s.r ≫ u0 ≫ K.φf.f 0 + H.φg.f 0 ≫ w0 ≫ t.s
  have sf : H.φf.f 0 ≫ s.r = 𝟙 _ := s.f_r
  have tg : t.s ≫ K.φg.f 0 = 𝟙 _ := t.s_g
  have hzero : H.φf.f 0 ≫ H.φg.f 0 = 0 :=
    HomologicalComplex.congr_hom H.w 0
  have kzero : K.φf.f 0 ≫ K.φg.f 0 = 0 :=
    HomologicalComplex.congr_hom K.w 0
  have hf : H.φf.f 0 ≫ b0 = u0 ≫ K.φf.f 0 := by
    dsimp only [b0]
    rw [comp_add, ← Category.assoc, sf, Category.id_comp,
      ← Category.assoc, hzero, zero_comp, add_zero]
  have hg : b0 ≫ K.φg.f 0 = H.φg.f 0 ≫ w0 := by
    dsimp only [b0]
    simp only [add_comp, Category.assoc]
    rw [kzero, comp_zero, comp_zero, tg, Category.comp_id, zero_add]
  let iH1 : S.X₁ ⟶ H.res₁.cocomplex.X 0 := H.res₁.ι.f 0
  let iH : S.X₂ ⟶ H.res₂.cocomplex.X 0 := H.res₂.ι.f 0
  let iH3 : S.X₃ ⟶ H.res₃.cocomplex.X 0 := H.res₃.ι.f 0
  let iK1 : T.X₁ ⟶ K.res₁.cocomplex.X 0 := K.res₁.ι.f 0
  let iK2 : T.X₂ ⟶ K.res₂.cocomplex.X 0 := K.res₂.ι.f 0
  let iK3 : T.X₃ ⟶ K.res₃.cocomplex.X 0 := K.res₃.ι.f 0
  have hlf : iH1 ≫ H.φf.f 0 = S.f ≫ iH := H.lift_f
  have hlg : iH ≫ H.φg.f 0 = S.g ≫ iH3 := H.lift_g
  have klf : iK1 ≫ K.φf.f 0 = T.f ≫ iK2 := K.lift_f
  have klg : iK2 ≫ K.φg.f 0 = T.g ≫ iK3 := K.lift_g
  have hu : iH1 ≫ u0 = α.τ₁ ≫ iK1 :=
    u.ι_f_zero_comp_hom_f_zero.trans (congrArg (· ≫ iK1)
      (CochainComplex.single₀_map_f_zero α.τ₁))
  have hw : iH3 ≫ w0 = α.τ₃ ≫ iK3 :=
    w.ι_f_zero_comp_hom_f_zero.trans (congrArg (· ≫ iK3)
      (CochainComplex.single₀_map_f_zero α.τ₃))
  let e : S.X₂ ⟶ K.res₂.cocomplex.X 0 :=
    α.τ₂ ≫ iK2 - iH ≫ b0
  have e_g : e ≫ K.φg.f 0 = 0 := by
    dsimp only [e]
    simp only [sub_comp, Category.assoc]
    rw [klg, hg, ← Category.assoc iH (H.φg.f 0), hlg]
    simp only [Category.assoc]
    rw [hw, ← Category.assoc, α.comm₂₃]
    simp only [Category.assoc, sub_self]
  let a : S.X₂ ⟶ K.res₁.cocomplex.X 0 := e ≫ t.r
  have af : a ≫ K.φf.f 0 = e := by
    dsimp only [a]
    have htr : t.r ≫ K.φf.f 0 = 𝟙 _ - K.φg.f 0 ≫ t.s := t.r_f
    rw [Category.assoc, htr, comp_sub, Category.comp_id, ← Category.assoc,
      e_g, zero_comp, sub_zero]
  have e_f : S.f ≫ e = 0 := by
    dsimp only [e]
    simp only [comp_sub, ← Category.assoc]
    rw [← α.comm₁₂, Category.assoc α.τ₁, ← klf, ← hlf]
    simp only [Category.assoc]
    rw [hf, ← Category.assoc α.τ₁ iK1, ← hu]
    simp only [Category.assoc]
    simp only [sub_self]
  have ha : S.f ≫ a = 0 := by simp [a, ← Category.assoc, e_f]
  let : Injective (K.res₁.cocomplex.X 0) := K.res₁.injective 0
  let q := hS.exact.descToInjective a ha
  have hq : S.g ≫ q = a := hS.exact.comp_descToInjective a ha
  let z := Injective.factorThru q iH3
  have hz : iH3 ≫ z = q := Injective.comp_factorThru q iH3
  let b : H.res₂.cocomplex.X 0 ⟶ K.res₂.cocomplex.X 0 := b0 + H.φg.f 0 ≫ z ≫ K.φf.f 0
  refine ⟨b, ?_, ?_, ?_⟩
  · dsimp only [b]
    simp only [comp_add, ← Category.assoc]
    rw [hf, hzero]
    simp only [zero_comp, add_zero]
    rfl
  · dsimp only [b]
    simp only [add_comp, Category.assoc]
    rw [hg, kzero]
    simp only [comp_zero, add_zero]
    rfl
  · change iH ≫ b = α.τ₂ ≫ iK2
    have hz' : iH ≫ (H.φg.f 0 ≫ z ≫ K.φf.f 0) = e := by
      calc
        _ = (iH ≫ H.φg.f 0) ≫ z ≫ K.φf.f 0 := by simp only [Category.assoc]
        _ = (S.g ≫ iH3) ≫ z ≫ K.φf.f 0 := by rw [hlg]
        _ = S.g ≫ (iH3 ≫ z) ≫ K.φf.f 0 := by simp only [Category.assoc]
        _ = (S.g ≫ q) ≫ K.φf.f 0 := by rw [hz]; simp only [Category.assoc]
        _ = a ≫ K.φf.f 0 := by rw [hq]
        _ = e := af
    dsimp only [b]
    rw [comp_add, hz']
    dsimp only [e]
    rw [add_comm, sub_add_cancel]

end CategoryTheory.Functor.RightDerived

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
universe u v
namespace CategoryTheory.Functor.RightDerived
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]

omit [HasInjectiveResolutions C] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Let `C` be abelian, `H,K` compatible injective horseshoe data
for short exact sequences `S,T`, and `α : S → T`. Fix maps of
endpoint injective resolutions `u : H₁ → K₁` over `α₁` and
`w : H₃ → K₃` over `α₃`. Suppose `bⁿ : H₂ⁿ → K₂ⁿ` commutes with both endpoint maps,
preserves the coaugmentation when `n=0`, and has a predecessor
compatible with the differential when `n>0`. It extends to `b^(n+1)`
commuting with both endpoints and satisfying
`d_H₂ ≫ b^(n+1) = bⁿ ≫ d_K₂`. -/
theorem HorseshoeData.nonempty_middle_succ_comparison
    {S T : ShortComplex C} {hS : S.ShortExact} {hT : T.ShortExact}
    (H : HorseshoeData S hS) (K : HorseshoeData T hT) (α : S ⟶ T)
    (u : InjectiveResolution.Hom H.res₁ K.res₁ α.τ₁)
    (w : InjectiveResolution.Hom H.res₃ K.res₃ α.τ₃) (n : ℕ)
    (b : H.res₂.cocomplex.X n ⟶ K.res₂.cocomplex.X n)
    (hf : H.φf.f n ≫ b = u.hom.f n ≫ K.φf.f n)
    (hg : b ≫ K.φg.f n = H.φg.f n ≫ w.hom.f n)
    (haug : ∀ hn : n = 0,
      (by subst n; exact H.res₂.ι.f 0 ≫ b = α.τ₂ ≫ K.res₂.ι.f 0))
    (hprev : ∀ m, m + 1 = n →
      ∃ c : H.res₂.cocomplex.X m ⟶ K.res₂.cocomplex.X m,
        H.res₂.cocomplex.d m n ≫ b = c ≫ K.res₂.cocomplex.d m n) :
    ∃ b' : H.res₂.cocomplex.X (n + 1) ⟶ K.res₂.cocomplex.X (n + 1),
      H.φf.f (n + 1) ≫ b' = u.hom.f (n + 1) ≫ K.φf.f (n + 1) ∧
      b' ≫ K.φg.f (n + 1) = H.φg.f (n + 1) ≫ w.hom.f (n + 1) ∧
      H.res₂.cocomplex.d n (n + 1) ≫ b' = b ≫ K.res₂.cocomplex.d n (n + 1) := by
  let s : (ShortComplex.mk (H.φf.f (n + 1)) (H.φg.f (n + 1))
      (HomologicalComplex.congr_hom H.w (n + 1))).Splitting := H.split (n + 1)
  let t : (ShortComplex.mk (K.φf.f (n + 1)) (K.φg.f (n + 1))
      (HomologicalComplex.congr_hom K.w (n + 1))).Splitting := K.split (n + 1)
  let c : H.res₂.cocomplex.X (n + 1) ⟶ K.res₂.cocomplex.X (n + 1) :=
    s.r ≫ u.hom.f (n + 1) ≫ K.φf.f (n + 1) +
      H.φg.f (n + 1) ≫ w.hom.f (n + 1) ≫ t.s
  have hzero : H.φf.f (n + 1) ≫ H.φg.f (n + 1) = 0 :=
    HomologicalComplex.congr_hom H.w (n + 1)
  have kzero : K.φf.f (n + 1) ≫ K.φg.f (n + 1) = 0 :=
    HomologicalComplex.congr_hom K.w (n + 1)
  have cf : H.φf.f (n + 1) ≫ c = u.hom.f (n + 1) ≫ K.φf.f (n + 1) := by
    dsimp only [c]
    simp only [comp_add, ← Category.assoc]
    rw [s.f_r, hzero]
    simp only [Category.id_comp, zero_comp, add_zero]
  have cg : c ≫ K.φg.f (n + 1) = H.φg.f (n + 1) ≫ w.hom.f (n + 1) := by
    dsimp only [c]
    simp only [add_comp, Category.assoc]
    rw [kzero, comp_zero, comp_zero, t.s_g, Category.comp_id, zero_add]
  let e : H.res₂.cocomplex.X n ⟶ K.res₂.cocomplex.X (n + 1) :=
    b ≫ K.res₂.cocomplex.d n (n + 1) - H.res₂.cocomplex.d n (n + 1) ≫ c
  have eg : e ≫ K.φg.f (n + 1) = 0 := by
    have kg : K.res₂.cocomplex.d n (n + 1) ≫ K.φg.f (n + 1) =
        K.φg.f n ≫ K.res₃.cocomplex.d n (n + 1) := (K.φg.comm n (n + 1)).symm
    have hg' : H.res₂.cocomplex.d n (n + 1) ≫ H.φg.f (n + 1) =
        H.φg.f n ≫ H.res₃.cocomplex.d n (n + 1) := (H.φg.comm n (n + 1)).symm
    have ww : w.hom.f n ≫ K.res₃.cocomplex.d n (n + 1) =
        H.res₃.cocomplex.d n (n + 1) ≫ w.hom.f (n + 1) := w.hom.comm n (n + 1)
    have first : (b ≫ K.res₂.cocomplex.d n (n + 1)) ≫ K.φg.f (n + 1) =
        H.φg.f n ≫ H.res₃.cocomplex.d n (n + 1) ≫ w.hom.f (n + 1) := by
      calc
        _ = b ≫ (K.φg.f n ≫ K.res₃.cocomplex.d n (n + 1)) := by
          rw [Category.assoc, kg]
        _ = (H.φg.f n ≫ w.hom.f n) ≫ K.res₃.cocomplex.d n (n + 1) := by
          rw [← Category.assoc, hg]
        _ = _ := by rw [Category.assoc, ww]
    have second : (H.res₂.cocomplex.d n (n + 1) ≫ c) ≫ K.φg.f (n + 1) =
        H.φg.f n ≫ H.res₃.cocomplex.d n (n + 1) ≫ w.hom.f (n + 1) := by
      rw [Category.assoc, cg, ← Category.assoc, hg']
      simp only [Category.assoc]
    dsimp only [e]
    rw [sub_comp, first, second, sub_self]
  let t0 : (ShortComplex.mk (K.φf.f (n + 1)) (K.φg.f (n + 1)) kzero).Splitting := t
  let r0 : (ShortComplex.mk (H.φf.f n) (H.φg.f n)
    (HomologicalComplex.congr_hom H.w n)).Splitting := H.split n
  let a : H.res₂.cocomplex.X n ⟶ K.res₁.cocomplex.X (n + 1) := e ≫ t0.r
  have af : a ≫ K.φf.f (n + 1) = e := by
    dsimp only [a]
    rw [Category.assoc, t0.r_f, comp_sub, Category.comp_id, ← Category.assoc,
      eg, zero_comp, sub_zero]
  have ef : H.φf.f n ≫ e = 0 := by
    have ff : H.φf.f n ≫ H.res₂.cocomplex.d n (n + 1) =
        H.res₁.cocomplex.d n (n + 1) ≫ H.φf.f (n + 1) := H.φf.comm n (n + 1)
    have kf : K.φf.f n ≫ K.res₂.cocomplex.d n (n + 1) =
        K.res₁.cocomplex.d n (n + 1) ≫ K.φf.f (n + 1) := K.φf.comm n (n + 1)
    have uu : u.hom.f n ≫ K.res₁.cocomplex.d n (n + 1) =
        H.res₁.cocomplex.d n (n + 1) ≫ u.hom.f (n + 1) := u.hom.comm n (n + 1)
    have first : H.φf.f n ≫ (b ≫ K.res₂.cocomplex.d n (n + 1)) =
        H.res₁.cocomplex.d n (n + 1) ≫ u.hom.f (n + 1) ≫ K.φf.f (n + 1) := by
      rw [← Category.assoc, hf, Category.assoc, kf, ← Category.assoc, uu]
      simp only [Category.assoc]
    have second : H.φf.f n ≫ (H.res₂.cocomplex.d n (n + 1) ≫ c) =
        H.res₁.cocomplex.d n (n + 1) ≫ u.hom.f (n + 1) ≫ K.φf.f (n + 1) := by
      rw [← Category.assoc, ff, Category.assoc, cf]
    dsimp only [e]
    rw [comp_sub, first, second, sub_self]
  have ea : H.φf.f n ≫ a = 0 := by simp only [a, ← Category.assoc, ef, zero_comp]
  let q : H.res₃.cocomplex.X n ⟶ K.res₁.cocomplex.X (n + 1) := r0.s ≫ a
  have hq : H.φg.f n ≫ q = a := by
    dsimp only [q]
    rw [← Category.assoc, r0.g_s, sub_comp, Category.id_comp, Category.assoc,
      ea, comp_zero, sub_zero]
  let : Injective (K.res₁.cocomplex.X (n + 1)) := K.res₁.injective (n + 1)
  have qprev : ∀ m, m + 1 = n → H.res₃.cocomplex.d m n ≫ q = 0 := by
    intro m hm
    let sm : (ShortComplex.mk (H.φf.f m) (H.φg.f m)
      (HomologicalComplex.congr_hom H.w m)).Splitting := H.split m
    let : Epi (H.φg.f m) := sm.epi_g
    apply (cancel_epi (H.φg.f m)).1
    have hp : H.φg.f m ≫ (H.res₃.cocomplex.d m n ≫ q) =
        H.res₂.cocomplex.d m n ≫ a := by
      rw [← Category.assoc, H.φg.comm m n, Category.assoc, hq]
    rw [hp, comp_zero]
    obtain ⟨c0, hc0⟩ := hprev m hm
    have he : H.res₂.cocomplex.d m n ≫ e = 0 := by
      dsimp only [e]
      rw [comp_sub, ← Category.assoc, hc0]
      simp only [Category.assoc]
      rw [K.res₂.cocomplex.d_comp_d]
      rw [← Category.assoc (H.res₂.cocomplex.d m n)
        (H.res₂.cocomplex.d n (n + 1)), H.res₂.cocomplex.d_comp_d]
      simp only [comp_zero, zero_comp, sub_self]
    dsimp only [a]
    rw [← Category.assoc, he, zero_comp]
  let : Injective (K.res₁.cocomplex.X (n + 1)) := K.res₁.injective (n + 1)
  have nz : ∃ z : H.res₃.cocomplex.X (n + 1) ⟶ K.res₁.cocomplex.X (n + 1),
      H.res₃.cocomplex.d n (n + 1) ≫ z = q := by
    cases n with
    | zero =>
        have ha0 : H.res₃.ι.f 0 ≫ q = 0 := by
          let : Epi S.g := hS.epi_g
          apply (cancel_epi S.g).1
          have hp : S.g ≫ (H.res₃.ι.f 0 ≫ q) = H.res₂.ι.f 0 ≫ a := by
            rw [← Category.assoc, ← H.lift_g, Category.assoc, hq]
          rw [hp, comp_zero]
          have he : H.res₂.ι.f 0 ≫ e = 0 := by
            dsimp only [e]
            rw [comp_sub, ← Category.assoc, haug rfl]
            simp only [Category.assoc]
            rw [K.res₂.ι_f_zero_comp_complex_d,
              ← Category.assoc (H.res₂.ι.f 0) (H.res₂.cocomplex.d 0 1),
              H.res₂.ι_f_zero_comp_complex_d]
            simp only [comp_zero, zero_comp, sub_self]
          dsimp only [a]
          rw [← Category.assoc, he, zero_comp]
        exact ⟨H.res₃.exact₀.descToInjective q ha0,
          H.res₃.exact₀.comp_descToInjective q ha0⟩
    | succ m =>
        exact ⟨(H.res₃.exact_succ m).descToInjective q (qprev m rfl),
          (H.res₃.exact_succ m).comp_descToInjective q (qprev m rfl)⟩
  obtain ⟨z, hz⟩ := nz
  let b' := c + H.φg.f (n + 1) ≫ z ≫ K.φf.f (n + 1)
  refine ⟨b', ?_, ?_, ?_⟩
  · dsimp only [b']
    simp only [comp_add, ← Category.assoc]
    rw [cf, hzero]
    simp only [zero_comp, add_zero]
  · dsimp only [b']
    simp only [add_comp, Category.assoc]
    rw [cg, kzero]
    simp only [comp_zero, add_zero]
  · have he : H.res₂.cocomplex.d n (n + 1) ≫
        (H.φg.f (n + 1) ≫ z ≫ K.φf.f (n + 1)) = e := by
      calc
        _ = (H.φg.f n ≫ H.res₃.cocomplex.d n (n + 1)) ≫ z ≫ K.φf.f (n + 1) := by
          rw [← Category.assoc, (H.φg.comm n (n + 1)).symm]
        _ = H.φg.f n ≫ (H.res₃.cocomplex.d n (n + 1) ≫ z) ≫ K.φf.f (n + 1) := by
          simp only [Category.assoc]
        _ = (H.φg.f n ≫ q) ≫ K.φf.f (n + 1) := by rw [hz]; simp only [Category.assoc]
        _ = e := by rw [hq, af]
    dsimp only [b']
    rw [comp_add, he]
    dsimp only [e]
    exact (_root_.add_comm _ _).trans (sub_add_cancel _ _)

end CategoryTheory.Functor.RightDerived

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
universe u v
namespace CategoryTheory.Functor.RightDerived
variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Let `C` be abelian, `H,K` compatible injective horseshoe data
for short exact sequences `S,T`, and `α : S → T`. Fix maps of
endpoint injective resolutions `u : H₁ → K₁` over `α₁` and
`w : H₃ → K₃` over `α₃`. A middle prefix through degree `N` consists of maps `bⁿ`
for `n≤N` commuting with the endpoint maps, preserving the degree-zero
coaugmentation, and satisfying every differential equation within
those degrees. -/
structure HorseshoeData.MiddlePrefix
    {S T : ShortComplex C} {hS : S.ShortExact} {hT : T.ShortExact}
    (H : HorseshoeData S hS) (K : HorseshoeData T hT) (α : S ⟶ T)
    (u : InjectiveResolution.Hom H.res₁ K.res₁ α.τ₁)
    (w : InjectiveResolution.Hom H.res₃ K.res₃ α.τ₃) (N : ℕ) where
  /-- Let `C` be abelian, `H,K` compatible injective horseshoe data
for short exact sequences `S,T`, and `α : S → T`. Fix maps of
endpoint injective resolutions `u : H₁ → K₁` over `α₁` and
`w : H₃ → K₃` over `α₃`. The degree-`n` component of a middle prefix through `N`,
for `n≤N`, is a map `bⁿ : H₂ⁿ → K₂ⁿ` subject to its endpoint,
coaugmentation, and consecutive-degree differential equations. -/
  b (n : ℕ) (hn : n ≤ N) : H.res₂.cocomplex.X n ⟶ K.res₂.cocomplex.X n
  left n hn : H.φf.f n ≫ b n hn = u.hom.f n ≫ K.φf.f n
  right n hn : b n hn ≫ K.φg.f n = H.φg.f n ≫ w.hom.f n
  augmentation : H.res₂.ι.f 0 ≫ b 0 (Nat.zero_le N) = α.τ₂ ≫ K.res₂.ι.f 0
  differential n hn : H.res₂.cocomplex.d n (n + 1) ≫ b (n + 1) hn =
    b n (by omega) ≫ K.res₂.cocomplex.d n (n + 1)

namespace HorseshoeData
variable {S T : ShortComplex C} {hS : S.ShortExact} {hT : T.ShortExact}
variable (H : HorseshoeData S hS) (K : HorseshoeData T hT) (α : S ⟶ T)
variable (u : InjectiveResolution.Hom H.res₁ K.res₁ α.τ₁)
variable (w : InjectiveResolution.Hom H.res₃ K.res₃ α.τ₃)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Let `C` be abelian, `H,K` compatible injective horseshoe data
for short exact sequences `S,T`, and `α : S → T`. Fix maps of
endpoint injective resolutions `u : H₁ → K₁` over `α₁` and
`w : H₃ → K₃` over `α₃`. There is a compatible prefix in degree zero: its middle map
commutes with the fixed endpoint maps and preserves the coaugmentation. -/
def middlePrefixZero : MiddlePrefix H K α u w 0 := by
  let witness := H.nonempty_middle_zero_comparison K α u w
  let b := witness.choose
  have hl := witness.choose_spec.1
  have hr := witness.choose_spec.2.1
  have ha := witness.choose_spec.2.2
  exact {
    b := fun n hn => by
      have hn0 : n = 0 := by omega
      subst n
      exact b
    left := fun n hn => by
      have hn0 : n = 0 := by omega
      subst n
      exact hl
    right := fun n hn => by
      have hn0 : n = 0 := by omega
      subst n
      exact hr
    augmentation := ha
    differential := fun n hn => by omega }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Let `C` be abelian, `H,K` compatible injective horseshoe data
for short exact sequences `S,T`, and `α : S → T`. Fix maps of
endpoint injective resolutions `u : H₁ → K₁` over `α₁` and
`w : H₃ → K₃` over `α₃`. Any compatible middle prefix through degree `N` extends to
one through degree `N+1`, preserving its endpoint and coaugmentation
conditions and adding the last differential equation. -/
def middlePrefixSucc {N : ℕ} (P : MiddlePrefix H K α u w N) :
    MiddlePrefix H K α u w (N + 1) := by
  let witness := H.nonempty_middle_succ_comparison K α u w N
    (P.b N (le_refl N)) (P.left N _) (P.right N _)
    (by intro h; subst N; exact P.augmentation)
    (by
      intro m hm
      subst N
      exact ⟨P.b m (by omega), P.differential m (le_refl _)⟩)
  let z := witness.choose
  have hl := witness.choose_spec.1
  have hr := witness.choose_spec.2.1
  have hd := witness.choose_spec.2.2
  let b : ∀ n, n ≤ N + 1 → (H.res₂.cocomplex.X n ⟶ K.res₂.cocomplex.X n) :=
    fun n hn => if h : n ≤ N then P.b n h else by
      have he : n = N + 1 := by omega
      subst n
      exact z
  refine { b := b, left := ?_, right := ?_, augmentation := ?_, differential := ?_ }
  · intro n hn
    dsimp only [b]
    split_ifs with h
    · exact P.left n h
    · have he : n = N + 1 := by omega
      subst n
      exact hl
  · intro n hn
    dsimp only [b]
    split_ifs with h
    · exact P.right n h
    · have he : n = N + 1 := by omega
      subst n
      exact hr
  · dsimp only [b]
    rw [dite_eq_left (Nat.zero_le N)]
    exact P.augmentation
  · intro n hn
    by_cases h : n + 1 ≤ N
    · dsimp only [b]
      rw [dite_eq_left h, dite_eq_left (by omega)]
      exact P.differential n h
    · have he : n = N := by omega
      subst n
      dsimp only [b]
      rw [dite_eq_right (by omega), dite_eq_left (le_refl N)]
      exact hd

/-- Let `C` be abelian, `H,K` compatible injective horseshoe data
for short exact sequences `S,T`, and `α : S → T`. Fix maps of
endpoint injective resolutions `u : H₁ → K₁` over `α₁` and
`w : H₃ → K₃` over `α₃`. Extending a middle prefix through degree `N` preserves each
of its component maps in every degree `n≤N`. -/
@[simp] theorem middlePrefixSucc_b {N : ℕ} (P : MiddlePrefix H K α u w N)
    (n : ℕ) (hn : n ≤ N) :
    (middlePrefixSucc H K α u w P).b n (Nat.le_trans hn (Nat.le_succ N)) = P.b n hn := by
  unfold middlePrefixSucc
  simp only [dite_eq_left hn]

/-- Let `C` be abelian, `H,K` compatible injective horseshoe data
for short exact sequences `S,T`, and `α : S → T`. Fix maps of
endpoint injective resolutions `u : H₁ → K₁` over `α₁` and
`w : H₃ → K₃` over `α₃`. The degree-zero prefix and successive extensions give a
family of compatible middle prefixes through every finite degree `N`. -/
def middlePrefixes : ∀ N, MiddlePrefix H K α u w N
  | 0 => middlePrefixZero H K α u w
  | N + 1 => middlePrefixSucc H K α u w (middlePrefixes N)

/-- Let `C` be abelian, `H,K` compatible injective horseshoe data
for short exact sequences `S,T`, and `α : S → T`. Fix maps of
endpoint injective resolutions `u : H₁ → K₁` over `α₁` and
`w : H₃ → K₃` over `α₃`. For `n≤N`, the degree-`n` component of the prefix through
`N` equals the component of the prefix through `n`; successive
extensions therefore define a coherent family. -/
theorem middlePrefixes_stable (N n : ℕ) (hn : n ≤ N) :
    (middlePrefixes H K α u w N).b n hn =
      (middlePrefixes H K α u w n).b n (le_refl n) := by
  induction N with
  | zero =>
      have h : n = 0 := by omega
      subst n
      rfl
  | succ N ih =>
      by_cases h : n ≤ N
      · change (middlePrefixSucc H K α u w (middlePrefixes H K α u w N)).b n hn = _
        rw [middlePrefixSucc_b H K α u w _ n h]
        exact ih h
      · have he : n = N + 1 := by omega
        subst n
        rfl

/-- Let `C` be abelian, `H,K` compatible injective horseshoe data
for short exact sequences `S,T`, and `α : S → T`. Fix maps of
endpoint injective resolutions `u : H₁ → K₁` over `α₁` and
`w : H₃ → K₃` over `α₃`. The stable component in degree `n` is a map
`bⁿ : H₂ⁿ → K₂ⁿ` taken from the coherent compatible prefix through `n`. -/
def middleComponent (n : ℕ) : H.res₂.cocomplex.X n ⟶ K.res₂.cocomplex.X n :=
  (middlePrefixes H K α u w n).b n (le_refl n)

/-- Let `C` be abelian, `H,K` compatible injective horseshoe data
for short exact sequences `S,T`, and `α : S → T`. Fix maps of
endpoint injective resolutions `u : H₁ → K₁` over `α₁` and
`w : H₃ → K₃` over `α₃`. The stable middle components satisfy
`d_H₂ⁿ ≫ b^(n+1) = bⁿ ≫ d_K₂ⁿ` for every `n`, and hence commute
with the cochain differentials. -/
theorem middleComponent_differential (n : ℕ) :
    H.res₂.cocomplex.d n (n + 1) ≫ middleComponent H K α u w (n + 1) =
      middleComponent H K α u w n ≫ K.res₂.cocomplex.d n (n + 1) := by
  have h := (middlePrefixes H K α u w (n + 1)).differential n (le_refl _)
  rw [middlePrefixes_stable H K α u w (n + 1) n (Nat.le_succ n)] at h
  exact h

/-- Let `C` be abelian, `H,K` compatible injective horseshoe data
for short exact sequences `S,T`, and `α : S → T`. Fix maps of
endpoint injective resolutions `u : H₁ → K₁` over `α₁` and
`w : H₃ → K₃` over `α₃`. The stable components of the compatible prefixes assemble
into a full cochain map `H₂ → K₂` between the middle resolutions. -/
def middleComparison : H.res₂.cocomplex ⟶ K.res₂.cocomplex where
  f n := middleComponent H K α u w n
  comm' i j hij := by
    have hj : i + 1 = j := by simpa only [ComplexShape.up_Rel] using hij
    subst j
    exact (middleComponent_differential H K α u w i).symm

/-- Let `C` be abelian, `H,K` compatible injective horseshoe data
for short exact sequences `S,T`, and `α : S → T`. Fix maps of
endpoint injective resolutions `u : H₁ → K₁` over `α₁` and
`w : H₃ → K₃` over `α₃`. The given endpoint maps and the constructed middle cochain
map form a morphism of compatible horseshoe data over `α`. -/
def comparisonWithEndpoints : HorseshoeData.Hom H K α where
  ψ₁ := u.hom
  ψ₂ := middleComparison H K α u w
  ψ₃ := w.hom
  lift₁ := u.ι_f_zero_comp_hom_f_zero.trans
    (congrArg (· ≫ K.res₁.ι.f 0) (CochainComplex.single₀_map_f_zero α.τ₁))
  lift₂ := (middlePrefixes H K α u w 0).augmentation
  lift₃ := w.ι_f_zero_comp_hom_f_zero.trans
    (congrArg (· ≫ K.res₃.ι.f 0) (CochainComplex.single₀_map_f_zero α.τ₃))
  comm_φf := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact (middlePrefixes H K α u w n).left n (le_refl n)
  comm_φg := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact ((middlePrefixes H K α u w n).right n (le_refl n)).symm

variable [HasInjectiveResolutions C]

/-- Let `C,A` be abelian, with injective resolutions in `C`,
`F : C → A` additive, and `H,K` any compatible injective horseshoe
data for the same short exact sequence `S`. Their connecting maps
`R^nF(S.X₃) → R^(n+1)F(S.X₁)` are equal for every `n`. -/
theorem delta_eq {A : Type*} [Category* A] [Abelian A]
    {F : C ⥤ A} [F.Additive] (n : ℕ)
    (K' : HorseshoeData S hS) : H.delta F n (n + 1) rfl = K'.delta F n (n + 1) rfl := by
  let u' := InjectiveResolution.descHom (𝟙 S.X₁) H.res₁ K'.res₁
  let w' := InjectiveResolution.descHom (𝟙 S.X₃) H.res₃ K'.res₃
  have h := (comparisonWithEndpoints H K' (𝟙 S) u' w').delta_naturality F n (n + 1) rfl
  simpa only [ShortComplex.id_τ₁, ShortComplex.id_τ₃, Functor.map_id,
    Category.comp_id, Category.id_comp] using h

end HorseshoeData
end CategoryTheory.Functor.RightDerived

end
