/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MinimalFibration.MapHomotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetFibrationHomotopyExtension
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetFibrationPathComposition
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetIhomFibration
public import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryDesc
public import Mathlib.CategoryTheory.NatIso

/-!
# Rigidity of minimal simplicial fibrations

For a minimal Kan fibration p:E→B, two cylinders over the same base simplex that agree on the
entire boundary cylinder and at one endpoint agree at the other endpoint. A self-map of E
fiberwise homotopic to identity over p is therefore a simplicial isomorphism.

For minimal fibrations p:E→B and p′:E′→B, maps a:E→E′ and b:E′→E are isomorphisms if their two
composites are fiberwise homotopic to the respective identities. The results hold in any
simplicial-set universe u.

Joël Riou's minimal-fibration development identified this rigidity argument. References:
Goerss–Jardine, Simplicial Homotopy Theory, Chapter I, Section 10; Hovey, Model Categories,
Section 3.5.
-/

@[expose] public section

universe u

open CategoryTheory Limits Simplicial SSet HomotopicalAlgebra
open MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet
namespace MinimalFibration

variable {E B : SSet.{u}} {p : E ⟶ B}

/-- Let p:E→B be a minimal Kan fibration. A path in the internal hom from Δ[n] to E that is constant
under the comparison recording boundary restriction and base projection has equal uncurried
endpoint maps Δ[n]→E. -/
private theorem endpoint_eq_of_ihom_path
    (hp : IsMinimalFibration p) {n : ℕ}
    (φ : Δ[1] ⟶ (ihom Δ[n]).obj E)
    (a : (pullback ((ihom (boundary n : SSet.{u})).map p)
      ((pre (boundary n).ι).app B) : SSet.{u}) _⦋0⦌)
    (f g : Δ[n] ⟶ E)
    (hφ₀ : ι₀ ≫ uncurry φ = f)
    (hφ₁ : ι₁ ≫ uncurry φ = g)
    (hconst : φ ≫ ihomToPullback (boundary n).ι p = SSet.const a) :
    f = g := by
  let _ : Fibration p := hp.1
  obtain ⟨bd, base, sq, rfl⟩ :=
    ihomToPullbackTgt₀Mk_surjective (boundary n).ι p a
  have hBoundaryPath := hconst =≫
    pullback.fst ((ihom (boundary n : SSet.{u})).map p)
      ((pre (boundary n).ι).app B)
  simp only [Category.assoc, pullback.lift_fst, const_comp,
    pullback_fst_app_ihomToPullbackTgt₀Mk] at hBoundaryPath
  have hBasePath := hconst =≫
    pullback.snd ((ihom (boundary n : SSet.{u})).map p)
      ((pre (boundary n).ι).app B)
  simp only [Category.assoc, pullback.lift_snd, const_comp,
    pullback_snd_app_ihomToPullbackTgt₀Mk] at hBasePath
  have hBoundaryCylinder :
      ((boundary n).ι ▷ (Δ[1] : SSet.{u})) ≫ uncurry φ =
        fst (boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫ bd := by
    rw [← uncurry_pre_app, hBoundaryPath]
    rfl
  have hBoundary : (boundary n).ι ≫ f = bd := by
    calc
      (boundary n).ι ≫ f = (boundary n).ι ≫ (ι₀ ≫ uncurry φ) := by rw [hφ₀]
      _ = ι₀ ≫ (((boundary n).ι ▷ (Δ[1] : SSet.{u})) ≫ uncurry φ) := by
        rw [← Category.assoc, ← ι₀_comp, Category.assoc]
      _ = ι₀ ≫ (fst (boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫ bd) := by
        rw [hBoundaryCylinder]
      _ = bd := by simp
  let W : OverRelation p (yonedaEquiv f) (yonedaEquiv g) :=
    { hom :=
        { h := uncurry φ
          h₀ := by simpa only [Equiv.symm_apply_apply] using hφ₀
          h₁ := by simpa only [Equiv.symm_apply_apply] using hφ₁
          stationary := by
            intro m x hx t
            have hc := ConcreteCategory.congr_hom
              (congr_app hBoundaryCylinder m) ⟨⟨x, hx⟩, t⟩
            have hb := ConcreteCategory.congr_hom (congr_app hBoundary m) ⟨x, hx⟩
            change (uncurry φ).app m ⟨x, t⟩ = bd.app m ⟨x, hx⟩ at hc
            have hc' : (uncurry φ).app m ⟨x, t⟩ = bd.app m ⟨x, hx⟩ := by
              exact hc
            have hb' : f.app m x = bd.app m ⟨x, hx⟩ := by
              simpa using hb
            simpa only [Equiv.symm_apply_apply] using hc'.trans hb'.symm }
      base := base
      bd := bd
      over := by
        rw [← uncurry_natural_right, hBasePath]
        rfl
      boundary := by
        simpa only [Equiv.symm_apply_apply] using hBoundary }
  have h := W.eq hp.2
  exact yonedaEquiv.injective (by simpa only [Equiv.symm_apply_apply] using h)

/-- Let p:E→B be a minimal Kan fibration. Let h₁,h₂:Δ[n]×Δ[1]→E project to the same base n-simplex,
and agree on the entire boundary cylinder ∂Δ[n]×Δ[1]. If their endpoint-zero restrictions agree,
their endpoint-one restrictions also agree. -/
theorem congr_ι₁_comp (hp : IsMinimalFibration p) {n : ℕ}
    (h₁ h₂ : Δ[n] ⊗ Δ[1] ⟶ E) (b : B _⦋n⦌)
    (h₁b : h₁ ≫ p = fst _ _ ≫ yonedaEquiv.symm b)
    (h₂b : h₂ ≫ p = fst _ _ ≫ yonedaEquiv.symm b)
    (hbd : (boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ h₁ =
      (boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ h₂)
    (h₀ : ι₀ ≫ h₁ = ι₀ ≫ h₂) :
    ι₁ ≫ h₁ = ι₁ ≫ h₂ := by
  let _ : Fibration p := hp.1
  let q := ihomToPullback (boundary n).ι p
  let _ : Fibration q := fibration_ihomToPullback (boundary n).ι p
  obtain ⟨φ, a, hφ₀, hφ₁, hφq⟩ :=
    exists_path_composition₀_above_of_fibration' q (curry h₁) (curry h₂) (by
      apply uncurry_injective
      rw [uncurry_natural_left, uncurry_natural_left, uncurry_curry, uncurry_curry]
      apply (cancel_epi (stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv).mp
      simpa only [Category.assoc, stdSimplex.rightUnitor_inv_map_δ_one_assoc] using h₀) (by
      apply pullback.hom_ext
      · simp only [q, Category.assoc, pullback.lift_fst, curry_pre_app, hbd]
      · simp only [q, Category.assoc, pullback.lift_snd, ← curry_natural_right, h₁b, h₂b])
  apply endpoint_eq_of_ihom_path hp φ a (ι₁ ≫ h₁) (ι₁ ≫ h₂) ?_ ?_ hφq
  · calc
      ι₀ ≫ uncurry φ =
          (stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
            ((Δ[n] : SSet.{u}) ◁ stdSimplex.δ 1) ≫ uncurry φ := by
              rw [stdSimplex.rightUnitor_inv_map_δ_one_assoc]
      _ = (stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
            uncurry (stdSimplex.δ 1 ≫ φ) := by rw [uncurry_natural_left]
      _ = (stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
            uncurry (stdSimplex.δ 0 ≫ curry h₁) := by rw [hφ₀]
      _ = ι₁ ≫ h₁ := by
        rw [uncurry_natural_left, uncurry_curry,
          stdSimplex.rightUnitor_inv_map_δ_zero_assoc]
  · calc
      ι₁ ≫ uncurry φ =
          (stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
            ((Δ[n] : SSet.{u}) ◁ stdSimplex.δ 0) ≫ uncurry φ := by
              rw [stdSimplex.rightUnitor_inv_map_δ_zero_assoc]
      _ = (stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
            uncurry (stdSimplex.δ 0 ≫ φ) := by rw [uncurry_natural_left]
      _ = (stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
            uncurry (stdSimplex.δ 0 ≫ curry h₂) := by rw [hφ₁]
      _ = ι₁ ≫ h₂ := by
        rw [uncurry_natural_left, uncurry_curry,
          stdSimplex.rightUnitor_inv_map_δ_zero_assoc]

/-- Let p:E→B be a minimal Kan fibration. Let h₁,h₂:Δ[n]×Δ[1]→E project to the same base n-simplex,
and agree on the entire boundary cylinder ∂Δ[n]×Δ[1]. If their endpoint-one restrictions agree,
their endpoint-zero restrictions also agree. -/
theorem congr_ι₀_comp (hp : IsMinimalFibration p) {n : ℕ}
    (h₁ h₂ : Δ[n] ⊗ Δ[1] ⟶ E) (b : B _⦋n⦌)
    (h₁b : h₁ ≫ p = fst _ _ ≫ yonedaEquiv.symm b)
    (h₂b : h₂ ≫ p = fst _ _ ≫ yonedaEquiv.symm b)
    (hbd : (boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ h₁ =
      (boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ h₂)
    (h₁eq : ι₁ ≫ h₁ = ι₁ ≫ h₂) :
    ι₀ ≫ h₁ = ι₀ ≫ h₂ := by
  let _ : Fibration p := hp.1
  let q := ihomToPullback (boundary n).ι p
  let _ : Fibration q := fibration_ihomToPullback (boundary n).ι p
  obtain ⟨φ, a, hφ₀, hφ₁, hφq⟩ :=
    exists_path_composition₂_above_of_fibration' q (curry h₁) (curry h₂) (by
      apply uncurry_injective
      rw [uncurry_natural_left, uncurry_natural_left, uncurry_curry, uncurry_curry]
      apply (cancel_epi (stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv).mp
      simpa only [Category.assoc, stdSimplex.rightUnitor_inv_map_δ_zero_assoc] using h₁eq) (by
      apply pullback.hom_ext
      · simp only [q, Category.assoc, pullback.lift_fst, curry_pre_app, hbd]
      · simp only [q, Category.assoc, pullback.lift_snd, ← curry_natural_right, h₁b, h₂b])
  apply endpoint_eq_of_ihom_path hp φ a (ι₀ ≫ h₁) (ι₀ ≫ h₂) ?_ ?_ hφq
  · calc
      ι₀ ≫ uncurry φ =
          (stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
            ((Δ[n] : SSet.{u}) ◁ stdSimplex.δ 1) ≫ uncurry φ := by
              rw [stdSimplex.rightUnitor_inv_map_δ_one_assoc]
      _ = (stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
            uncurry (stdSimplex.δ 1 ≫ φ) := by rw [uncurry_natural_left]
      _ = (stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
            uncurry (stdSimplex.δ 1 ≫ curry h₁) := by rw [hφ₀]
      _ = ι₀ ≫ h₁ := by
        rw [uncurry_natural_left, uncurry_curry,
          stdSimplex.rightUnitor_inv_map_δ_one_assoc]
  · calc
      ι₁ ≫ uncurry φ =
          (stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
            ((Δ[n] : SSet.{u}) ◁ stdSimplex.δ 0) ≫ uncurry φ := by
              rw [stdSimplex.rightUnitor_inv_map_δ_zero_assoc]
      _ = (stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
            uncurry (stdSimplex.δ 0 ≫ φ) := by rw [uncurry_natural_left]
      _ = (stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
            uncurry (stdSimplex.δ 1 ≫ curry h₂) := by rw [hφ₁]
      _ = ι₀ ≫ h₂ := by
        rw [uncurry_natural_left, uncurry_curry,
          stdSimplex.rightUnitor_inv_map_δ_one_assoc]

end MinimalFibration

namespace FiberwiseHomotopy

variable {E B : SSet.{u}} {p : E ⟶ B} {u : E ⟶ E}

/-- Let p:E→B be a minimal Kan fibration. Let a:E→E have a fiberwise homotopy a→id_E over p. The
component aₙ is injective in every simplicial degree n. -/
theorem injective_app_of_isMinimalFibration
    (H : FiberwiseHomotopy p p u (𝟙 E))
    (hp : MinimalFibration.IsMinimalFibration p)
    (n : SimplexCategoryᵒᵖ) : Function.Injective (u.app n) := by
  obtain ⟨n⟩ := n
  induction n using SimplexCategory.rec with
  | _ d =>
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro s₁ s₂ hs
      have hbase : p.app _ s₁ = p.app _ s₂ := by
        calc
          p.app _ s₁ = (u ≫ p).app _ s₁ := by rw [H.fac₀]
          _ = p.app _ (u.app _ s₁) := rfl
          _ = p.app _ (u.app _ s₂) := congrArg (p.app _) hs
          _ = (u ≫ p).app _ s₂ := rfl
          _ = p.app _ s₂ := by rw [H.fac₀]
      let b : B _⦋d⦌ := p.app _ s₁
      let K₁ : Δ[d] ⊗ Δ[1] ⟶ E :=
        (yonedaEquiv.symm s₁ ▷ (Δ[1] : SSet.{u})) ≫ H.hom.h
      let K₂ : Δ[d] ⊗ Δ[1] ⟶ E :=
        (yonedaEquiv.symm s₂ ▷ (Δ[1] : SSet.{u})) ≫ H.hom.h
      have hK₁base : K₁ ≫ p = fst _ _ ≫ yonedaEquiv.symm b := by
        simp only [K₁, Category.assoc, H.over, whiskerRight_fst_assoc,
          yonedaEquiv_symm_comp, b]
      have hK₂base : K₂ ≫ p = fst _ _ ≫ yonedaEquiv.symm b := by
        simp only [K₂, Category.assoc, H.over, whiskerRight_fst_assoc,
          yonedaEquiv_symm_comp, b]
        rw [hbase]
      have hBoundaryMaps :
          (boundary d).ι ≫ yonedaEquiv.symm s₁ =
            (boundary d).ι ≫ yonedaEquiv.symm s₂ := by
        obtain _ | d := d
        · exact boundary.hom_ext₀
        · apply boundary.hom_ext
          intro j
          simp only [boundary.ι_ι_assoc, stdSimplex.δ_comp_yonedaEquiv_symm]
          apply congrArg yonedaEquiv.symm
          apply ih d (by simp)
          simpa only [SSet.δ_naturality_apply] using congrArg (fun z ↦ E.δ j z) hs
      have hKBoundary :
          (boundary d).ι ▷ (Δ[1] : SSet.{u}) ≫ K₁ =
            (boundary d).ι ▷ (Δ[1] : SSet.{u}) ≫ K₂ := by
        simp only [K₁, K₂, ← MonoidalCategory.comp_whiskerRight_assoc,
          hBoundaryMaps]
      have hKZero : ι₀ ≫ K₁ = ι₀ ≫ K₂ := by
        simp only [K₁, K₂, ι₀_comp_assoc, H.hom.h₀, yonedaEquiv_symm_comp]
        rw [hs]
      have hKOne := MinimalFibration.congr_ι₁_comp hp K₁ K₂ b
        hK₁base hK₂base hKBoundary hKZero
      apply yonedaEquiv.symm.injective
      simpa only [K₁, K₂, ι₁_comp_assoc, H.hom.h₁, Category.comp_id] using hKOne

/-- Let p:E→B be a minimal Kan fibration. Let a:E→E have a fiberwise homotopy a→id_E over p. The
component aₙ is surjective in every simplicial degree n. -/
theorem surjective_app_of_isMinimalFibration
    (H : FiberwiseHomotopy p p u (𝟙 E))
    (hp : MinimalFibration.IsMinimalFibration p)
    (n : SimplexCategoryᵒᵖ) : Function.Surjective (u.app n) := by
  let _ : Fibration p := hp.1
  obtain ⟨n⟩ := n
  induction n using SimplexCategory.rec with
  | _ d =>
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro x
      obtain ⟨y, hy⟩ :
          ∃ y : (boundary d : SSet.{u}) ⟶ E,
            y ≫ u = (boundary d).ι ≫ yonedaEquiv.symm x := by
        obtain _ | d := d
        · exact ⟨(boundary 0).ι ≫ yonedaEquiv.symm x, boundary.hom_ext₀⟩
        · let s (i : Fin (d + 2)) : E _⦋d⦌ :=
            (ih d (by simp) (E.δ i x)).choose
          have hs (i : Fin (d + 2)) : u.app _ (s i) = E.δ i x :=
            (ih d (by simp) (E.δ i x)).choose_spec
          obtain _ | d := d
          · let faces : Fin 2 → ((Δ[0] : SSet.{u}) ⟶ E) :=
              fun i ↦ yonedaEquiv.symm (s i)
            have hfaces : boundary.IsCompatible faces := True.intro
            let y : (boundary 1 : SSet.{u}) ⟶ E := hfaces.desc
            refine ⟨y, boundary.hom_ext (fun i ↦ ?_)⟩
            rw [← Category.assoc, hfaces.ι_desc, yonedaEquiv_symm_comp, hs,
              boundary.ι_ι_assoc, stdSimplex.δ_comp_yonedaEquiv_symm]
          · let faces : Fin (d + 3) → ((Δ[d + 1] : SSet.{u}) ⟶ E) :=
              fun i ↦ yonedaEquiv.symm (s i)
            have hfaces : boundary.IsCompatible faces := by
              rw [boundary.isCompatible_succ_iff]
              intro j k hjk
              simp only [faces, stdSimplex.δ_comp_yonedaEquiv_symm]
              apply congrArg yonedaEquiv.symm
              apply H.injective_app_of_isMinimalFibration hp (Opposite.op ⦋d⦌)
              simp only [SSet.δ_naturality_apply, hs]
              obtain ⟨k, rfl⟩ := k.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hjk)
              obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hjk)
              simp only [Fin.pred_succ, Fin.castPred_castSucc]
              rw [← Fin.le_castSucc_iff, Fin.castSucc_le_castSucc_iff] at hjk
              exact (E.δ_comp_δ_apply hjk x).symm
            let y : (boundary (d + 2) : SSet.{u}) ⟶ E := hfaces.desc
            refine ⟨y, boundary.hom_ext (fun i ↦ ?_)⟩
            rw [← Category.assoc, hfaces.ι_desc, yonedaEquiv_symm_comp, hs,
              boundary.ι_ι_assoc, stdSimplex.δ_comp_yonedaEquiv_symm]
      let hBoundary : (boundary d : SSet.{u}) ⊗ Δ[1] ⟶ E :=
        (y ▷ (Δ[1] : SSet.{u})) ≫ H.hom.h
      let f : Δ[d] ⟶ E := yonedaEquiv.symm x
      let hBase : Δ[d] ⊗ Δ[1] ⟶ B := fst _ _ ≫ f ≫ p
      have hyp : y ≫ p = (boundary d).ι ≫ f ≫ p := by
        calc
          y ≫ p = y ≫ (u ≫ p) := by rw [H.fac₀]
          _ = (y ≫ u) ≫ p := by rw [Category.assoc]
          _ = (boundary d).ι ≫ f ≫ p := by rw [hy]; rfl
      obtain ⟨Φ, hΦ₀, hΦbd, hΦp⟩ := homotopy_extension_property₀
        (boundary d).ι p hBoundary f (by
          simp only [hBoundary, f, ι₀_comp_assoc, H.hom.h₀]
          exact hy.symm) hBase (by simp [hBase, f]) (by
          calc
            (boundary d).ι ▷ (Δ[1] : SSet.{u}) ≫ hBase =
                fst (boundary d : SSet.{u}) (Δ[1] : SSet.{u}) ≫
                  (boundary d).ι ≫ f ≫ p := by simp [hBase]
            _ = fst (boundary d : SSet.{u}) (Δ[1] : SSet.{u}) ≫ y ≫ p := by
              rw [hyp]
            _ = (y ▷ (Δ[1] : SSet.{u})) ≫ fst E (Δ[1] : SSet.{u}) ≫ p := by
              rw [whiskerRight_fst_assoc]
            _ = hBoundary ≫ p := by simp [hBoundary, H.over])
      let z : E _⦋d⦌ := yonedaEquiv (ι₁ ≫ Φ)
      let K : Δ[d] ⊗ Δ[1] ⟶ E :=
        (yonedaEquiv.symm z ▷ (Δ[1] : SSet.{u})) ≫ H.hom.h
      have hzmap : yonedaEquiv.symm z = ι₁ ≫ Φ := by
        simp only [z, Equiv.symm_apply_apply]
      have hzbase : yonedaEquiv.symm z ≫ p = yonedaEquiv.symm x ≫ p := by
        calc
          yonedaEquiv.symm z ≫ p = (ι₁ ≫ Φ) ≫ p := by rw [hzmap]
          _ = ι₁ ≫ (Φ ≫ p) := by rw [Category.assoc]
          _ = ι₁ ≫ hBase := by rw [hΦp]
          _ = yonedaEquiv.symm x ≫ p := by simp [hBase, f]
      have hKbase : K ≫ p = fst _ _ ≫ yonedaEquiv.symm (p.app _ x) := by
        calc
          K ≫ p = fst _ _ ≫ (yonedaEquiv.symm z ≫ p) := by
            simp [K, H.over]
          _ = fst _ _ ≫ (yonedaEquiv.symm x ≫ p) := by rw [hzbase]
          _ = fst _ _ ≫ yonedaEquiv.symm (p.app _ x) := by
            rw [yonedaEquiv_symm_comp]
      have hΦbase : Φ ≫ p = fst _ _ ≫ yonedaEquiv.symm (p.app _ x) := by
        simpa only [hBase, f, Category.assoc, yonedaEquiv_symm_comp] using hΦp
      have hzboundary : (boundary d).ι ≫ yonedaEquiv.symm z = y := by
        calc
          (boundary d).ι ≫ yonedaEquiv.symm z = (boundary d).ι ≫ (ι₁ ≫ Φ) := by
            rw [hzmap]
          _ = ι₁ ≫ (((boundary d).ι ▷ (Δ[1] : SSet.{u})) ≫ Φ) := by
            rw [← Category.assoc, ← ι₁_comp, Category.assoc]
          _ = ι₁ ≫ hBoundary := by rw [hΦbd]
          _ = y := by simp [hBoundary]
      have hKboundary :
          (boundary d).ι ▷ (Δ[1] : SSet.{u}) ≫ Φ =
            (boundary d).ι ▷ (Δ[1] : SSet.{u}) ≫ K := by
        rw [hΦbd]
        simp only [hBoundary, K, ← MonoidalCategory.comp_whiskerRight_assoc,
          hzboundary]
      have hEndpoint : ι₁ ≫ Φ = ι₁ ≫ K := by
        simp only [K, ι₁_comp_assoc, H.hom.h₁, Category.comp_id, hzmap]
      have hZero := MinimalFibration.congr_ι₀_comp hp Φ K (p.app _ x)
        hΦbase hKbase hKboundary hEndpoint
      refine ⟨z, ?_⟩
      apply yonedaEquiv.symm.injective
      calc
        yonedaEquiv.symm (u.app _ z) = ι₀ ≫ K := by
          simp [K, yonedaEquiv_symm_comp]
        _ = ι₀ ≫ Φ := hZero.symm
        _ = yonedaEquiv.symm x := hΦ₀

/-- Let p:E→B be a minimal Kan fibration. Let a:E→E have a fiberwise homotopy a→id_E over p. The map
a is a simplicial isomorphism. -/
theorem isIso_of_isMinimalFibration
    (H : FiberwiseHomotopy p p u (𝟙 E))
    (hp : MinimalFibration.IsMinimalFibration p) : IsIso u := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  rw [CategoryTheory.isIso_iff_bijective]
  exact ⟨H.injective_app_of_isMinimalFibration hp n,
    H.surjective_app_of_isMinimalFibration hp n⟩

end FiberwiseHomotopy

namespace MinimalFibration

/-- Let p:E→B and p′:E′→B be minimal Kan fibrations, and a:E→E′, b:E′→E maps. If a≫b is fiberwise
homotopic to id_E over p and b≫a to id_E′ over p′, then a is an isomorphism. -/
theorem isIso_of_fiberwiseHomotopyEquiv {E E' B : SSet.{u}}
    (p : E ⟶ B) (p' : E' ⟶ B)
    (hp : IsMinimalFibration p) (hp' : IsMinimalFibration p')
    (u : E ⟶ E') (v : E' ⟶ E)
    (huv : SSet.FiberwiseHomotopy p p (u ≫ v) (𝟙 E))
    (hvu : SSet.FiberwiseHomotopy p' p' (v ≫ u) (𝟙 E')) : IsIso u := by
  let _ : IsIso (u ≫ v) := huv.isIso_of_isMinimalFibration hp
  let _ : IsIso (v ≫ u) := hvu.isIso_of_isMinimalFibration hp'
  let _ : Mono u := mono_of_mono u v
  let _ : Epi u := epi_of_epi v u
  exact isIso_of_mono_of_epi u

end MinimalFibration
end SSet
