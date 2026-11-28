/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney.Coherence
public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Associativity of front/back cosimplicial pairings

In a monoidal category, a degreewise pairing of cosimplicial objects commuting with cofaces is
natural for all injective simplex maps. The front/back pairing in degrees p,q is obtained by
mapping the front p-face and back q-face into degree p+q and then applying the degreewise
pairing. For three factors, front, middle and back inclusions identify the two parenthesizations
whenever the degreewise products satisfy the associativity square.
-/

@[expose] public section
set_option autoImplicit false
universe uC vC
open CategoryTheory MonoidalCategory AlgebraicTopology

namespace AlgebraicTopology.CosimplicialCup

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]

set_option backward.isDefEq.respectTransparency.types false in
/-- Let C be monoidal, A,B,D cosimplicial objects, and m_n : Aⁿ⊗Bⁿ → Dⁿ satisfy (δ_i^A⊗δ_i^B) ≫
m_{n+1} = m_n ≫ δ_i^D for every n ∈ ℕ and i ∈ Fin(n+2). For every injective simplex map f : [r]
→ [s], (A(f)⊗B(f)) ≫ m_s = m_r ≫ D(f). -/
theorem pairing_naturality_mono (A B D : CosimplicialObject C)
    (m : ∀ n, A.obj (SimplexCategory.mk n) ⊗ B.obj (SimplexCategory.mk n) ⟶
      D.obj (SimplexCategory.mk n))
    (hm : ∀ n (i : Fin (n + 2)), (A.δ i ⊗ₘ B.δ i) ≫ m (n + 1) = m n ≫ D.δ i)
    {x y : SimplexCategory} (f : x ⟶ y) [Mono f] :
    (A.map f ⊗ₘ B.map f) ≫ m y.len = m x.len ≫ D.map f := by
  let P : MorphismProperty SimplexCategory :=
    fun x y f => (A.map f ⊗ₘ B.map f) ≫ m y.len = m x.len ≫ D.map f
  apply SimplexCategory.mono_induction (motive := P) ?_ ?_ f
  · intro x
    dsimp only [P]
    simp only [A.map_id, B.map_id, D.map_id, tensorHom_id, id_whiskerRight,
      Category.id_comp, Category.comp_id]
  · intro x y f i hf
    dsimp only [P] at hf ⊢
    have hδ : (A.map (SimplexCategory.δ i) ⊗ₘ B.map (SimplexCategory.δ i)) ≫
        m (y.len + 1) = m y.len ≫ D.map (SimplexCategory.δ i) := hm y.len i
    simp only [Functor.map_comp]
    rw [← tensorHom_comp_tensorHom, Category.assoc, hδ, ← Category.assoc, hf, Category.assoc]

/-- Let C be monoidal, A,B,D cosimplicial objects, and m_n : Aⁿ⊗Bⁿ → Dⁿ any degreewise maps. For
p,q,n ∈ ℕ with p+q=n, awPair is A^p⊗B^q → D^n obtained by applying A to the front inclusion [p]
→ [n], applying B to the back inclusion [q] → [n], tensoring these maps and then applying m_n.
This definition requires no coface compatibility of m. -/
def awPair (A B D : CosimplicialObject C)
    (m : ∀ n, A.obj (SimplexCategory.mk n) ⊗ B.obj (SimplexCategory.mk n) ⟶
      D.obj (SimplexCategory.mk n)) (p q n : ℕ) (h : p + q = n) :
    A.obj (SimplexCategory.mk p) ⊗ B.obj (SimplexCategory.mk q) ⟶ D.obj (SimplexCategory.mk n) :=
  (A.map (AlexanderWhitney.frontInclusion p q n h) ⊗ₘ
    B.map (AlexanderWhitney.backInclusion p q n h)) ≫ m n

private theorem front_mono (p q n : ℕ) (h : p + q = n) :
    Mono (AlexanderWhitney.frontInclusion p q n h) := by
  apply SimplexCategory.mono_iff_injective.mpr
  intro i j hij
  apply Fin.ext
  have hh := congrArg Fin.val hij
  simpa only [AlexanderWhitney.frontInclusion_toOrderHom] using hh

private theorem back_mono (p q n : ℕ) (h : p + q = n) :
    Mono (AlexanderWhitney.backInclusion p q n h) := by
  apply SimplexCategory.mono_iff_injective.mpr
  intro i j hij
  apply Fin.ext
  have hh := congrArg Fin.val hij
  simp only [AlexanderWhitney.backInclusion_toOrderHom] at hh
  omega

set_option backward.isDefEq.respectTransparency.types false in
/-- Let C be monoidal and A,B,F,AB,BF,D_L,D_R cosimplicial objects, with degreewise maps m_AB : A⊗B
→ AB, m_BF : B⊗F → BF, m_L : AB⊗F → D_L and m_R : A⊗BF → D_R. Assume m_AB and m_BF commute with
all cofaces. Let e : D_L → D_R be a cosimplicial map such that in every degree (m_AB⊗id_F) ≫ m_L
≫ e = α ≫ (id_A⊗m_BF) ≫ m_R, where α is the tensor associator. Then for p,q,r,n ∈ ℕ with
(p+q)+r=n, (AW_AB,p,q⊗id_{F^r}) ≫ AW_L,p+q,r ≫ e_n = α_{A^p,B^q,F^r} ≫ (id_{A^p}⊗AW_BF,q,r) ≫
AW_R,p,q+r. No coface law on m_L or m_R is assumed. -/
theorem awPair_assoc
    (A B C' AB BC DL DR : CosimplicialObject C)
    (mAB : ∀ n,
        A.obj (SimplexCategory.mk n) ⊗ B.obj (SimplexCategory.mk n) ⟶
        AB.obj (SimplexCategory.mk n))
    (mBC : ∀ n,
        B.obj (SimplexCategory.mk n) ⊗ C'.obj (SimplexCategory.mk n) ⟶
        BC.obj (SimplexCategory.mk n))
    (mL : ∀ n,
        AB.obj (SimplexCategory.mk n) ⊗ C'.obj (SimplexCategory.mk n) ⟶
        DL.obj (SimplexCategory.mk n))
    (mR : ∀ n,
        A.obj (SimplexCategory.mk n) ⊗ BC.obj (SimplexCategory.mk n) ⟶
        DR.obj (SimplexCategory.mk n))
    (hmAB : ∀ n (i : Fin (n + 2)), (A.δ i ⊗ₘ B.δ i) ≫ mAB (n + 1) = mAB n ≫ AB.δ i)
    (hmBC : ∀ n (i : Fin (n + 2)), (B.δ i ⊗ₘ C'.δ i) ≫ mBC (n + 1) = mBC n ≫ BC.δ i)
    (e : DL ⟶ DR)
    (hm : ∀ n,
      (mAB n ⊗ₘ 𝟙 (C'.obj (SimplexCategory.mk n))) ≫ mL n ≫ e.app (SimplexCategory.mk n) =
      (α_ (A.obj (SimplexCategory.mk n)) (B.obj (SimplexCategory.mk n))
          (C'.obj (SimplexCategory.mk n))).hom ≫
        (𝟙 (A.obj (SimplexCategory.mk n)) ⊗ₘ mBC n) ≫ mR n)
    (p q r n : ℕ) (h : (p + q) + r = n) :
    (awPair A B AB mAB p q (p + q) rfl ⊗ₘ 𝟙 (C'.obj (SimplexCategory.mk r))) ≫
      awPair AB C' DL mL (p + q) r n h ≫ e.app (SimplexCategory.mk n) =
      (α_ (A.obj (SimplexCategory.mk p)) (B.obj (SimplexCategory.mk q))
          (C'.obj (SimplexCategory.mk r))).hom ≫
      (𝟙 (A.obj (SimplexCategory.mk p)) ⊗ₘ awPair B C' BC mBC q r (q + r) rfl) ≫
      awPair A BC DR mR p (q + r) n (by omega) := by
  let fAB := AlexanderWhitney.frontInclusion (p + q) r n h
  let fC := AlexanderWhitney.backInclusion (p + q) r n h
  let fA := AlexanderWhitney.frontInclusion p (q + r) n (by omega)
  let fBC := AlexanderWhitney.backInclusion p (q + r) n (by omega)
  let fAp := AlexanderWhitney.frontInclusion p q (p + q) rfl
  let fBq := AlexanderWhitney.backInclusion p q (p + q) rfl
  let fBq' := AlexanderWhitney.frontInclusion q r (q + r) rfl
  let fCr := AlexanderWhitney.backInclusion q r (q + r) rfl
  let : Mono fAB := front_mono (p + q) r n h
  let : Mono fBC := back_mono p (q + r) n (by omega)
  have hnL : (A.map fAB ⊗ₘ B.map fAB) ≫ mAB n = mAB (p + q) ≫ AB.map fAB :=
    pairing_naturality_mono A B AB mAB hmAB fAB
  have hnR : (B.map fBC ⊗ₘ C'.map fBC) ≫ mBC n = mBC (q + r) ≫ BC.map fBC :=
    pairing_naturality_mono B C' BC mBC hmBC fBC
  have hA : A.map fAp ≫ A.map fAB = A.map fA :=
    (A.map_comp fAp fAB).symm.trans
      (congrArg A.map (AlexanderWhitney.frontInclusion_assoc p q r n h))
  have hB : B.map fBq ≫ B.map fAB = B.map fBq' ≫ B.map fBC :=
    (B.map_comp fBq fAB).symm.trans
      ((congrArg B.map (AlexanderWhitney.middleInclusion_assoc p q r n h)).trans
        (B.map_comp fBq' fBC))
  have hC : C'.map fCr ≫ C'.map fBC = C'.map fC :=
    (C'.map_comp fCr fBC).symm.trans
      (congrArg C'.map (AlexanderWhitney.backInclusion_assoc p q r n h))
  unfold awPair
  change (((A.map fAp ⊗ₘ B.map fBq) ≫ mAB (p + q)) ⊗ₘ 𝟙 (C'.obj (SimplexCategory.mk r))) ≫
      ((AB.map fAB ⊗ₘ C'.map fC) ≫ mL n) ≫ e.app (SimplexCategory.mk n) =
    (α_ (A.obj (SimplexCategory.mk p)) (B.obj (SimplexCategory.mk q))
        (C'.obj (SimplexCategory.mk r))).hom ≫
      (𝟙 (A.obj (SimplexCategory.mk p)) ⊗ₘ ((B.map fBq' ⊗ₘ C'.map fCr) ≫ mBC (q + r))) ≫
      (A.map fA ⊗ₘ BC.map fBC) ≫ mR n
  have hl : (((A.map fAp ⊗ₘ B.map fBq) ≫ mAB (p + q)) ⊗ₘ
      𝟙 (C'.obj (SimplexCategory.mk r))) ≫ (AB.map fAB ⊗ₘ C'.map fC) =
      ((A.map fAp ⊗ₘ B.map fBq) ≫ (A.map fAB ⊗ₘ B.map fAB) ≫ mAB n) ⊗ₘ C'.map fC := by
    rw [tensorHom_comp_tensorHom, Category.id_comp, Category.assoc, ← hnL]
  have hr : (𝟙 (A.obj (SimplexCategory.mk p)) ⊗ₘ
      ((B.map fBq' ⊗ₘ C'.map fCr) ≫ mBC (q + r))) ≫ (A.map fA ⊗ₘ BC.map fBC) =
      A.map fA ⊗ₘ ((B.map fBq' ⊗ₘ C'.map fCr) ≫ (B.map fBC ⊗ₘ C'.map fBC) ≫ mBC n) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp, Category.assoc, ← hnR]
  simp only [Category.assoc]
  rw [← Category.assoc
    (((A.map fAp ⊗ₘ B.map fBq) ≫ mAB (p + q)) ⊗ₘ 𝟙 (C'.obj (SimplexCategory.mk r))), hl]
  rw [← Category.assoc
    (𝟙 (A.obj (SimplexCategory.mk p)) ⊗ₘ ((B.map fBq' ⊗ₘ C'.map fCr) ≫ mBC (q + r))), hr]
  have hleft : (A.map fAp ⊗ₘ B.map fBq) ≫ (A.map fAB ⊗ₘ B.map fAB) =
      A.map fA ⊗ₘ (B.map fBq' ≫ B.map fBC) := by
    rw [tensorHom_comp_tensorHom, hA, hB]
  have hright : (B.map fBq' ⊗ₘ C'.map fCr) ≫ (B.map fBC ⊗ₘ C'.map fBC) =
      (B.map fBq' ≫ B.map fBC) ⊗ₘ C'.map fC := by
    rw [tensorHom_comp_tensorHom, hC]
  have hleft' : (A.map fAp ⊗ₘ B.map fBq) ≫ (A.map fAB ⊗ₘ B.map fAB) ≫ mAB n =
      (A.map fA ⊗ₘ (B.map fBq' ≫ B.map fBC)) ≫ mAB n :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ mAB n) hleft)
  have hright' : (B.map fBq' ⊗ₘ C'.map fCr) ≫ (B.map fBC ⊗ₘ C'.map fBC) ≫ mBC n =
      ((B.map fBq' ≫ B.map fBC) ⊗ₘ C'.map fC) ≫ mBC n :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ mBC n) hright)
  rw [hleft', hright']
  let fB := B.map fBq' ≫ B.map fBC
  have hl' : ((A.map fA ⊗ₘ fB) ≫ mAB n) ⊗ₘ C'.map fC =
      ((A.map fA ⊗ₘ fB) ⊗ₘ C'.map fC) ≫
        (mAB n ⊗ₘ 𝟙 (C'.obj (SimplexCategory.mk n))) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  have hr' : A.map fA ⊗ₘ ((fB ⊗ₘ C'.map fC) ≫ mBC n) =
      (A.map fA ⊗ₘ (fB ⊗ₘ C'.map fC)) ≫
        (𝟙 (A.obj (SimplexCategory.mk n)) ⊗ₘ mBC n) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  rw [hl', hr']
  simp only [Category.assoc]
  rw [hm n]
  have ha := associator_naturality (A.map fA) fB (C'.map fC)
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫ (𝟙 (A.obj (SimplexCategory.mk n)) ⊗ₘ mBC n) ≫ mR n) ha


end AlgebraicTopology.CosimplicialCup
