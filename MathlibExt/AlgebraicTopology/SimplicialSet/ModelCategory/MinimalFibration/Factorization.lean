/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MinimalFibration.Existence
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MinimalFibration.Rigidity
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetFibrationHomotopyExtension

/-!
# Factorization through a minimal simplicial fibration

Let p:E→B be a Kan fibration and choose a minimal deformation subfibration M→B. The retraction
r:E→M has right lifting against every boundary inclusion. Thus p factors as r followed by the
minimal fibration M→B.

For a boundary square of r, extend the reversed deformation from the boundary across a simplex.
The endpoint-one map has the prescribed boundary, and minimality supplies its required
r-composite. The result is valid in any simplicial-set universe u.

References: Goerss–Jardine, Simplicial Homotopy Theory, Chapter I, Section 10; Hovey, Model Categories, Section 3.5.
-/

@[expose] public section

open CategoryTheory Simplicial SSet HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace SSet
namespace MinimalFibration

variable {E B : SSet.{u}} {p : E ⟶ B}

/-- Let p:E→B be a Kan fibration and M⊆E a minimal subfibration with inclusion ι and strong
deformation retraction r over B. The deformation id_E→r≫ι gives a relative homotopy over B
stationary on M. -/
private noncomputable def MinimalSubfibration.forwardHomotopyRelOver
    (M : MinimalSubfibration p) :
    HomotopyRelOver p (𝟙 E) (M.sdr.r ≫ M.carrier.ι) M.carrier where
  toHomotopyRel :=
    { h := M.sdr.homotopy.h
      h₀ := M.sdr.homotopy.h₀
      h₁ := M.sdr.homotopy.h₁
      stationary := by
        intro n x hx t
        exact M.sdr.homotopy.stationary x (by
          simpa only [Subfunctor.range_ι] using hx) t }
  over := by
    simpa only [Category.id_comp] using M.over

/-- Let p:E→B be a Kan fibration and M⊆E a minimal subfibration with inclusion ι and strong
deformation retraction r over B. Reverse that relative homotopy to obtain r≫ι→id_E over B, still
stationary on M. -/
private noncomputable def MinimalSubfibration.reverseHomotopyRelOver
    [Fibration p] (M : MinimalSubfibration p) :
    HomotopyRelOver p (M.sdr.r ≫ M.carrier.ι) (𝟙 E) M.carrier :=
  M.forwardHomotopyRelOver.symm

/-- Let p:E→B be a Kan fibration and M⊆E a minimal subfibration with inclusion ι and strong
deformation retraction r over B. For a boundary square of r with top ∂Δ[n]→E and bottom Δ[n]→M,
extend the reversed boundary deformation to Φ:Δ[n]×Δ[1]→E. It starts at bottom followed by ι,
restricts to the boundary deformation, and projects over B to the fixed base simplex of bottom. -/
private theorem MinimalSubfibration.exists_lifting_homotopy
    [Fibration p] (M : MinimalSubfibration p) {n : ℕ}
    (top : (boundary n : SSet.{u}) ⟶ E)
    (bottom : Δ[n] ⟶ (M.carrier : SSet.{u}))
    (sq : CommSq top (boundary n).ι M.sdr.r bottom) :
    ∃ Φ : Δ[n] ⊗ Δ[1] ⟶ E,
      ι₀ ≫ Φ = bottom ≫ M.carrier.ι ∧
      (boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ Φ =
        (top ▷ (Δ[1] : SSet.{u})) ≫ M.reverseHomotopyRelOver.h ∧
      Φ ≫ p = fst _ _ ≫ bottom ≫ (M.carrier.ι ≫ p) := by
  let K := M.reverseHomotopyRelOver
  apply homotopy_extension_property₀ (boundary n).ι p
    ((top ▷ (Δ[1] : SSet.{u})) ≫ K.h)
    (bottom ≫ M.carrier.ι)
  · simp only [ι₀_comp_assoc, K, HomotopyRelOver.h₀]
    exact ((reassoc_of% sq.w) M.carrier.ι).symm
  · simp
  · have hri : (M.sdr.r ≫ M.carrier.ι) ≫ p = p :=
      M.fiberwiseHomotopy.fac₁
    have hsq : (boundary n).ι ≫ bottom = top ≫ M.sdr.r := sq.w.symm
    calc
      (boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫
          (fst _ _ ≫ bottom ≫ (M.carrier.ι ≫ p)) =
          fst (boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
            (((boundary n).ι ≫ bottom) ≫
              (M.carrier.ι ≫ p)) := by
            simp only [Category.assoc, whiskerRight_fst_assoc]
      _ = fst (boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
            ((top ≫ M.sdr.r) ≫ (M.carrier.ι ≫ p)) := by
            rw [hsq]
      _ = fst (boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
            (top ≫ ((M.sdr.r ≫ M.carrier.ι) ≫ p)) := by
            simp only [Category.assoc]
      _ = fst (boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
            (top ≫ p) := by rw [hri]
      _ = (top ▷ (Δ[1] : SSet.{u})) ≫
            (fst E (Δ[1] : SSet.{u}) ≫
              ((M.sdr.r ≫ M.carrier.ι) ≫ p)) := by
            rw [hri]
            simp only [whiskerRight_fst_assoc]
      _ = (top ▷ (Δ[1] : SSet.{u})) ≫ (K.h ≫ p) := by
            exact congrArg (fun z ↦ (top ▷ (Δ[1] : SSet.{u})) ≫ z)
              K.over.symm
      _ = ((top ▷ (Δ[1] : SSet.{u})) ≫ K.h) ≫ p := by
            rw [Category.assoc]

/-- Let p:E→B be a Kan fibration and M⊆E a minimal subfibration with inclusion ι and strong
deformation retraction r over B. If Φ restricts on the boundary to the reversed deformation of
the top map, then its endpoint-one map has boundary equal to that top map. -/
private theorem MinimalSubfibration.lift_fac_left
    [Fibration p] (M : MinimalSubfibration p) {n : ℕ}
    (top : (boundary n : SSet.{u}) ⟶ E)
    (Φ : Δ[n] ⊗ Δ[1] ⟶ E)
    (hΦbd : (boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ Φ =
      (top ▷ (Δ[1] : SSet.{u})) ≫ M.reverseHomotopyRelOver.h) :
    (boundary n).ι ≫ (ι₁ ≫ Φ) = top := by
  calc
    (boundary n).ι ≫ (ι₁ ≫ Φ) =
        ι₁ ≫ (((boundary n).ι ▷ (Δ[1] : SSet.{u})) ≫ Φ) := by
          rw [← Category.assoc, ← ι₁_comp, Category.assoc]
    _ = ι₁ ≫ ((top ▷ (Δ[1] : SSet.{u})) ≫
        M.reverseHomotopyRelOver.h) := by rw [hΦbd]
    _ = top ≫ (ι₁ ≫ M.reverseHomotopyRelOver.h) := by
      rw [← Category.assoc, ι₁_comp, Category.assoc]
    _ = top := by rw [HomotopyRelOver.h₁, Category.comp_id]

/-- Let p:E→B be a Kan fibration and M⊆E a minimal subfibration with inclusion ι and strong
deformation retraction r over B. For the boundary lifting square and a cylinder Φ starting at
bottom≫ι, with its prescribed boundary and base projection, the endpoint-one map has r-composite
equal to bottom. Minimality of M→B gives this lifting triangle. -/
private theorem MinimalSubfibration.lift_fac_right
    [Fibration p] (M : MinimalSubfibration p) {n : ℕ}
    (top : (boundary n : SSet.{u}) ⟶ E)
    (bottom : Δ[n] ⟶ (M.carrier : SSet.{u}))
    (Φ : Δ[n] ⊗ Δ[1] ⟶ E)
    (hΦ₀ : ι₀ ≫ Φ = bottom ≫ M.carrier.ι)
    (hΦbd : (boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ Φ =
      (top ▷ (Δ[1] : SSet.{u})) ≫ M.reverseHomotopyRelOver.h)
    (hΦp : Φ ≫ p = fst _ _ ≫ bottom ≫ (M.carrier.ι ≫ p))
    (hleft : (boundary n).ι ≫ (ι₁ ≫ Φ) = top) :
    (ι₁ ≫ Φ) ≫ M.sdr.r = bottom := by
  let K := M.reverseHomotopyRelOver
  let lift : Δ[n] ⟶ E := ι₁ ≫ Φ
  let p' : (M.carrier : SSet.{u}) ⟶ B := M.carrier.ι ≫ p
  let q₁ : Δ[n] ⊗ Δ[1] ⟶ (M.carrier : SSet.{u}) :=
    (lift ▷ (Δ[1] : SSet.{u})) ≫ K.h ≫ M.sdr.r
  let q₂ : Δ[n] ⊗ Δ[1] ⟶ (M.carrier : SSet.{u}) :=
    Φ ≫ M.sdr.r
  let b : B.obj (Opposite.op (SimplexCategory.mk n)) :=
    yonedaEquiv (bottom ≫ p')
  have hrp : M.sdr.r ≫ p' = p := by
    dsimp only [p']
    rw [← Category.assoc, M.fiberwiseHomotopy.fac₁]
  have hliftp : lift ≫ p = bottom ≫ p' := by
    dsimp only [lift]
    calc
      (ι₁ ≫ Φ) ≫ p = ι₁ ≫ (Φ ≫ p) := by rw [Category.assoc]
      _ = ι₁ ≫ (fst _ _ ≫ bottom ≫ p') := by rw [hΦp]
      _ = bottom ≫ p' := by simp
  have hq₁base : q₁ ≫ p' = fst _ _ ≫ yonedaEquiv.symm b := by
    calc
      q₁ ≫ p' = (lift ▷ (Δ[1] : SSet.{u})) ≫
          (K.h ≫ (M.sdr.r ≫ p')) := by
            simp only [q₁, Category.assoc]
      _ = (lift ▷ (Δ[1] : SSet.{u})) ≫ (K.h ≫ p) := by rw [hrp]
      _ = (lift ▷ (Δ[1] : SSet.{u})) ≫
          (fst E (Δ[1] : SSet.{u}) ≫
            ((M.sdr.r ≫ M.carrier.ι) ≫ p)) := by
              exact congrArg
                (fun z ↦ (lift ▷ (Δ[1] : SSet.{u})) ≫ z) K.over
      _ = (lift ▷ (Δ[1] : SSet.{u})) ≫
          (fst E (Δ[1] : SSet.{u}) ≫ p) := by
            rw [M.fiberwiseHomotopy.fac₁]
      _ = fst _ _ ≫ (lift ≫ p) := by
            simp only [whiskerRight_fst_assoc]
      _ = fst _ _ ≫ (bottom ≫ p') := by rw [hliftp]
      _ = fst _ _ ≫ yonedaEquiv.symm b := by
            simp only [b, Equiv.symm_apply_apply]
  have hq₂base : q₂ ≫ p' = fst _ _ ≫ yonedaEquiv.symm b := by
    calc
      q₂ ≫ p' = Φ ≫ (M.sdr.r ≫ p') := by
        simp only [q₂, Category.assoc]
      _ = Φ ≫ p := by rw [hrp]
      _ = fst _ _ ≫ bottom ≫ (M.carrier.ι ≫ p) := hΦp
      _ = fst _ _ ≫ (bottom ≫ p') := by rfl
      _ = fst _ _ ≫ yonedaEquiv.symm b := by
        simp only [b, Equiv.symm_apply_apply]
  have hqBoundary :
      (boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ q₁ =
        (boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ q₂ := by
    simp only [q₁, q₂, ← MonoidalCategory.comp_whiskerRight_assoc]
    rw [hleft]
    exact ((reassoc_of% hΦbd) M.sdr.r).symm
  have hqEndpoint : ι₁ ≫ q₁ = ι₁ ≫ q₂ := by
    calc
      ι₁ ≫ q₁ = lift ≫ ((ι₁ ≫ K.h) ≫ M.sdr.r) := by
        simp only [q₁, ι₁_comp_assoc, Category.assoc]
      _ = lift ≫ ((𝟙 E) ≫ M.sdr.r) := by rw [K.h₁]
      _ = lift ≫ M.sdr.r := by rw [Category.id_comp]
      _ = ι₁ ≫ q₂ := by simp only [q₂, lift, Category.assoc]
  have hzero := congr_ι₀_comp M.isMinimalFibration q₁ q₂ b
    hq₁base hq₂base hqBoundary hqEndpoint
  change lift ≫ M.sdr.r = bottom
  have hq₁zero : ι₀ ≫ q₁ = lift ≫ M.sdr.r := by
    calc
      ι₀ ≫ q₁ = lift ≫ ((ι₀ ≫ K.h) ≫ M.sdr.r) := by
        simp only [q₁, ι₀_comp_assoc, Category.assoc]
      _ = lift ≫ ((M.sdr.r ≫ M.carrier.ι) ≫ M.sdr.r) := by
        rw [K.h₀]
      _ = lift ≫ (M.sdr.r ≫ (M.carrier.ι ≫ M.sdr.r)) := by
        exact congrArg (fun z ↦ lift ≫ z)
          (Category.assoc M.sdr.r M.carrier.ι M.sdr.r)
      _ = lift ≫ (M.sdr.r ≫ 𝟙 _) := by rw [M.sdr.retract]
      _ = lift ≫ M.sdr.r := by rw [Category.comp_id]
  have hq₂zero : ι₀ ≫ q₂ = bottom := by
    calc
      ι₀ ≫ q₂ = (ι₀ ≫ Φ) ≫ M.sdr.r := by
        simp only [q₂, Category.assoc]
      _ = (bottom ≫ M.carrier.ι) ≫ M.sdr.r := by rw [hΦ₀]
      _ = bottom ≫ (M.carrier.ι ≫ M.sdr.r) := by rw [Category.assoc]
      _ = bottom := by rw [M.sdr.retract, Category.comp_id]
  exact hq₁zero.symm.trans (hzero.trans hq₂zero)

/-- Let p:E→B be a Kan fibration and M⊆E a minimal subfibration with inclusion ι and strong
deformation retraction r over B. The retraction r:E→M has right lifting against every simplicial
boundary inclusion. -/
theorem MinimalSubfibration.retraction_mem_I_rlp
    {p : E ⟶ B} [Fibration p] (M : MinimalSubfibration p) :
    modelCategoryQuillen.I.{u}.rlp M.sdr.r := by
  rintro _ _ _ ⟨n⟩
  constructor
  intro top bottom sq
  obtain ⟨Φ, hΦ₀, hΦbd, hΦp⟩ := M.exists_lifting_homotopy top bottom sq
  let lift : Δ[n] ⟶ E := ι₁ ≫ Φ
  have hleft : (boundary n).ι ≫ lift = top :=
    M.lift_fac_left top Φ hΦbd
  have hright : lift ≫ M.sdr.r = bottom :=
    M.lift_fac_right top bottom Φ hΦ₀ hΦbd hΦp hleft
  exact CommSq.HasLift.mk' ⟨lift, hleft, hright⟩

/-- Every Kan fibration p:E→B factors as r:E→E′ followed by p′:E′→B, with r≫p′=p, p′ a minimal Kan
fibration and r having right lifting against all boundary inclusions. -/
theorem factorization (p : E ⟶ B) [Fibration p] :
    ∃ (E' : SSet.{u}) (r : E ⟶ E') (p' : E' ⟶ B),
      r ≫ p' = p ∧ IsMinimalFibration p' ∧
        modelCategoryQuillen.I.{u}.rlp r := by
  obtain ⟨M⟩ := nonempty_minimalSubfibration p
  refine ⟨(M.carrier : SSet.{u}), M.sdr.r, M.carrier.ι ≫ p, ?_,
    M.isMinimalFibration, M.retraction_mem_I_rlp⟩
  simpa only [Category.assoc] using M.fiberwiseHomotopy.fac₁

end MinimalFibration
end SSet
