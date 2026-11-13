/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.ConformalLinearMap
public import MathlibExt.Geometry.Manifold.Diffeomorph
public import MathlibExt.Geometry.Manifold.Riemannian.Conformal

/-!
# Isometric and conformal diffeomorphisms

Isometric and conformal diffeomorphisms between `C^∞` Riemannian manifolds,
their isometry and conformal groups, the `G`-invariant conformal class, and
the bridge to Mathlib conformal linear maps.

Main definitions: `Manifold.IsIsometryDiffeomorph`,
`Manifold.IsConformalDiffeomorph`, `Manifold.ConformallyEquivalent`,
`Manifold.isometryGroup`, `Manifold.conformalGroup`,
`Manifold.invariantConformalClass`.

Sources:
* Madani, *Equivariant Yamabe problem and Hebey-Vaugon conjecture*,
  J. Funct. Anal. 258 (2010): `I(M,g)` the isometry group, `C(M,g)` the
  conformal transformations group, `[g]^G` the invariant conformal class
* Encyclopedia of Mathematics, "Yamabe problem" (T. Aubin): conformal maps
  as isometric maps of a conformally changed metric
* Curry and Gover (arXiv:1412.7559), Definition 1.1, conformal class.
-/

@[expose] public section

open scoped Manifold ContDiff Bundle

noncomputable section

namespace Manifold

section TwoManifolds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- A diffeomorphism with pullback metric equal to the source metric. -/
def IsIsometryDiffeomorph
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (g' : Bundle.ContMDiffRiemannianMetric I' ∞ E' (fun x : M' ↦ TangentSpace I' x))
    (φ : M ≃ₘ^∞⟮I, I'⟯ M') : Prop :=
  ∀ x (v w : TangentSpace I x),
    g'.inner (φ x) (mfderiv I I' ⇑φ x v) (mfderiv I I' ⇑φ x w) = g.inner x v w

/-- A diffeomorphism with pullback metric a smooth positive multiple. -/
def IsConformalDiffeomorph
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (g' : Bundle.ContMDiffRiemannianMetric I' ∞ E' (fun x : M' ↦ TangentSpace I' x))
    (φ : M ≃ₘ^∞⟮I, I'⟯ M') : Prop :=
  ∃ u : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ u ∧ (∀ x, 0 < u x) ∧
    ∀ x (v w : TangentSpace I x),
      g'.inner (φ x) (mfderiv I I' ⇑φ x v) (mfderiv I I' ⇑φ x w) =
        u x * g.inner x v w

/-- An isometry is conformal with constant factor one. -/
theorem IsIsometryDiffeomorph.isConformalDiffeomorph
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {g' : Bundle.ContMDiffRiemannianMetric I' ∞ E' (fun x : M' ↦ TangentSpace I' x)}
    {φ : M ≃ₘ^∞⟮I, I'⟯ M'} (h : IsIsometryDiffeomorph g g' φ) :
    IsConformalDiffeomorph g g' φ := by
  refine ⟨fun _ ↦ 1, contMDiff_const, fun _ ↦ zero_lt_one, ?_⟩
  intro x v w
  have hx : g'.inner (φ x) (mfderiv I I' ⇑φ x v) (mfderiv I I' ⇑φ x w) =
    g.inner x v w := h x v w
  rw [hx, one_mul]

/-- Two metrics related by a conformal diffeomorphism. -/
def ConformallyEquivalent
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (g' : Bundle.ContMDiffRiemannianMetric I' ∞ E' (fun x : M' ↦ TangentSpace I' x)) :
    Prop :=
  ∃ φ : M ≃ₘ^∞⟮I, I'⟯ M', IsConformalDiffeomorph g g' φ

end TwoManifolds

section Groups

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Madani's `I(M,g)`: self-diffeomorphisms preserving `g`. -/
def isometryGroup
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    Subgroup (M ≃ₘ^∞⟮I, I⟯ M) where
  carrier := {φ | IsIsometryDiffeomorph g g φ}
  mul_mem' := by
    intro a b ha hb
    change IsIsometryDiffeomorph g g (a * b)
    intro x v w
    have hne : (∞ : ℕ∞ω) ≠ 0 := by simp
    have hb_x : MDifferentiableAt I I ⇑b x := (b.mdifferentiable hne) x
    have ha_bx : MDifferentiableAt I I ⇑a (b x) := (a.mdifferentiable hne) (b x)
    have hch : ∀ u : TangentSpace I x, mfderiv I I (⇑a ∘ ⇑b) x u =
        mfderiv I I ⇑a (b x) (mfderiv I I ⇑b x u) :=
      fun u => mfderiv_comp_apply x ha_bx hb_x u
    have hcoe : ⇑(a * b) = ⇑a ∘ ⇑b := Diffeomorph.coe_mul a b
    have hpt : (a * b) x = a (b x) := rfl
    have e1 : g.inner (a (b x))
        (mfderiv I I ⇑a (b x) (mfderiv I I ⇑b x v))
        (mfderiv I I ⇑a (b x) (mfderiv I I ⇑b x w)) =
        g.inner (b x) (mfderiv I I ⇑b x v) (mfderiv I I ⇑b x w) := ha (b x) _ _
    have e2 : g.inner (b x) (mfderiv I I ⇑b x v) (mfderiv I I ⇑b x w) =
      g.inner x v w := hb x v w
    rw [hpt, hcoe, hch v, hch w, e1, e2]
  one_mem' := by
    change IsIsometryDiffeomorph g g 1
    intro x v w
    have hcoe : ⇑(1 : M ≃ₘ^∞⟮I, I⟯ M) = id := Diffeomorph.coe_one
    have hderiv : mfderiv I I ⇑(1 : M ≃ₘ^∞⟮I, I⟯ M) x =
        ContinuousLinearMap.id ℝ (TangentSpace I x) := by
      rw [hcoe, mfderiv_id]
    have hpt : (1 : M ≃ₘ^∞⟮I, I⟯ M) x = x := rfl
    have hv : (ContinuousLinearMap.id ℝ (TangentSpace I x)) v = v := rfl
    have hw : (ContinuousLinearMap.id ℝ (TangentSpace I x)) w = w := rfl
    rw [hpt, hderiv, hv, hw]
  inv_mem' := by
    intro a ha
    change IsIsometryDiffeomorph g g a⁻¹
    intro y v w
    have hne : (∞ : ℕ∞ω) ≠ 0 := by simp
    have hsym_y : MDifferentiableAt I I ⇑(a.symm) y := (a.symm.mdifferentiable hne) y
    have ha_x : MDifferentiableAt I I ⇑a (a.symm y) := (a.mdifferentiable hne) (a.symm y)
    have hcomp : ∀ t : TangentSpace I y, mfderiv I I ⇑a (a.symm y)
        (mfderiv I I ⇑(a.symm) y t) = t := by
      intro t
      have hch : mfderiv I I (⇑a ∘ ⇑(a.symm)) y t =
          mfderiv I I ⇑a (a.symm y) (mfderiv I I ⇑(a.symm) y t) :=
        mfderiv_comp_apply y ha_x hsym_y t
      have hid : (⇑a ∘ ⇑(a.symm) : M → M) = id := funext fun z ↦ a.apply_symm_apply z
      rw [hid, mfderiv_id] at hch
      exact hch.symm
    have hbase : g.inner (a (a.symm y))
        (mfderiv I I ⇑a (a.symm y) (mfderiv I I ⇑(a.symm) y v))
        (mfderiv I I ⇑a (a.symm y) (mfderiv I I ⇑(a.symm) y w)) =
        g.inner (a.symm y) (mfderiv I I ⇑(a.symm) y v)
          (mfderiv I I ⇑(a.symm) y w) := ha (a.symm y) _ _
    have hay : a (a.symm y) = y := a.apply_symm_apply y
    rw [hcomp v, hcomp w, hay] at hbase
    have hpt : a⁻¹ y = a.symm y := rfl
    have e1 : mfderiv I I ⇑(a⁻¹) y v = mfderiv I I ⇑(a.symm) y v := rfl
    have e2 : mfderiv I I ⇑(a⁻¹) y w = mfderiv I I ⇑(a.symm) y w := rfl
    rw [hpt, e1, e2]
    exact hbase.symm

/-- Madani's `C(M,g)`: self-diffeomorphisms conformal for `g`. -/
def conformalGroup
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    Subgroup (M ≃ₘ^∞⟮I, I⟯ M) where
  carrier := {φ | IsConformalDiffeomorph g g φ}
  mul_mem' := by
    intro a b ha hb
    obtain ⟨uφ, huφ, hposφ, hφeq⟩ := (ha : IsConformalDiffeomorph g g a)
    obtain ⟨uψ, huψ, hposψ, hψeq⟩ := (hb : IsConformalDiffeomorph g g b)
    have hu_new : ContMDiff I 𝓘(ℝ) ∞ (fun x ↦ uφ (b x) * uψ x) :=
      (huφ.comp b.contMDiff).mul huψ
    have hpos_new : ∀ x, 0 < uφ (b x) * uψ x :=
      fun x ↦ mul_pos (hposφ (b x)) (hposψ x)
    refine ⟨fun x ↦ uφ (b x) * uψ x, hu_new, hpos_new, ?_⟩
    intro x v w
    have hne : (∞ : ℕ∞ω) ≠ 0 := by simp
    have hb_x : MDifferentiableAt I I ⇑b x := (b.mdifferentiable hne) x
    have ha_bx : MDifferentiableAt I I ⇑a (b x) := (a.mdifferentiable hne) (b x)
    have hch : ∀ u : TangentSpace I x, mfderiv I I (⇑a ∘ ⇑b) x u =
        mfderiv I I ⇑a (b x) (mfderiv I I ⇑b x u) :=
      fun u => mfderiv_comp_apply x ha_bx hb_x u
    have hcoe : ⇑(a * b) = ⇑a ∘ ⇑b := Diffeomorph.coe_mul a b
    have hpt : (a * b) x = a (b x) := rfl
    have eφ : g.inner (a (b x))
        (mfderiv I I ⇑a (b x) (mfderiv I I ⇑b x v))
        (mfderiv I I ⇑a (b x) (mfderiv I I ⇑b x w)) =
        uφ (b x) * g.inner (b x) (mfderiv I I ⇑b x v)
          (mfderiv I I ⇑b x w) := hφeq (b x) _ _
    have eψ : g.inner (b x) (mfderiv I I ⇑b x v) (mfderiv I I ⇑b x w) =
      uψ x * g.inner x v w := hψeq x v w
    rw [hpt, hcoe, hch v, hch w, eφ, eψ, mul_assoc]
  one_mem' := by
    refine ⟨fun _ ↦ 1, contMDiff_const, fun _ ↦ zero_lt_one, ?_⟩
    intro x v w
    have hcoe : ⇑(1 : M ≃ₘ^∞⟮I, I⟯ M) = id := Diffeomorph.coe_one
    have hderiv : mfderiv I I ⇑(1 : M ≃ₘ^∞⟮I, I⟯ M) x =
        ContinuousLinearMap.id ℝ (TangentSpace I x) := by
      rw [hcoe, mfderiv_id]
    have hpt : (1 : M ≃ₘ^∞⟮I, I⟯ M) x = x := rfl
    have hv : (ContinuousLinearMap.id ℝ (TangentSpace I x)) v = v := rfl
    have hw : (ContinuousLinearMap.id ℝ (TangentSpace I x)) w = w := rfl
    rw [hpt, hderiv, hv, hw]
    exact (one_mul _).symm
  inv_mem' := by
    intro a ha
    obtain ⟨u, hu, hpos, hueq⟩ := (ha : IsConformalDiffeomorph g g a)
    have hne_u : ∀ x, u x ≠ 0 := fun x ↦ ne_of_gt (hpos x)
    have hu_comp : ContMDiff I 𝓘(ℝ) ∞ (u ∘ ⇑(a.symm)) := hu.comp a.symm.contMDiff
    have hu_inv : ContMDiff I 𝓘(ℝ) ∞ (fun y ↦ (u (a.symm y))⁻¹) :=
      hu_comp.inv₀ (fun y ↦ hne_u (a.symm y))
    refine ⟨fun y ↦ (u (a.symm y))⁻¹, hu_inv, ?_, ?_⟩
    · intro y
      exact inv_pos.mpr (hpos (a.symm y))
    · intro y v w
      have hne : (∞ : ℕ∞ω) ≠ 0 := by simp
      have hsym_y : MDifferentiableAt I I ⇑(a.symm) y := (a.symm.mdifferentiable hne) y
      have ha_x : MDifferentiableAt I I ⇑a (a.symm y) := (a.mdifferentiable hne) (a.symm y)
      have hcomp : ∀ t : TangentSpace I y, mfderiv I I ⇑a (a.symm y)
          (mfderiv I I ⇑(a.symm) y t) = t := by
        intro t
        have hch : mfderiv I I (⇑a ∘ ⇑(a.symm)) y t =
            mfderiv I I ⇑a (a.symm y) (mfderiv I I ⇑(a.symm) y t) :=
          mfderiv_comp_apply y ha_x hsym_y t
        have hid : (⇑a ∘ ⇑(a.symm) : M → M) = id := funext fun z ↦ a.apply_symm_apply z
        rw [hid, mfderiv_id] at hch
        exact hch.symm
      have hbase : g.inner (a (a.symm y))
          (mfderiv I I ⇑a (a.symm y) (mfderiv I I ⇑(a.symm) y v))
          (mfderiv I I ⇑a (a.symm y) (mfderiv I I ⇑(a.symm) y w)) =
          u (a.symm y) * g.inner (a.symm y) (mfderiv I I ⇑(a.symm) y v)
            (mfderiv I I ⇑(a.symm) y w) := hueq (a.symm y) _ _
      have hay : a (a.symm y) = y := a.apply_symm_apply y
      rw [hcomp v, hcomp w, hay] at hbase
      have hx_ne : u (a.symm y) ≠ 0 := hne_u (a.symm y)
      have hpt : a⁻¹ y = a.symm y := rfl
      have e1 : mfderiv I I ⇑(a⁻¹) y v = mfderiv I I ⇑(a.symm) y v := rfl
      have e2 : mfderiv I I ⇑(a⁻¹) y w = mfderiv I I ⇑(a.symm) y w := rfl
      rw [hpt, e1, e2]
      have hcalc : (u (a.symm y))⁻¹ * g.inner y v w =
          g.inner (a.symm y) (mfderiv I I ⇑(a.symm) y v)
            (mfderiv I I ⇑(a.symm) y w) := by
        rw [hbase, ← mul_assoc, inv_mul_cancel₀ hx_ne, one_mul]
      exact hcalc.symm

/-- Membership in the isometry group is the isometry predicate. -/
@[simp]
theorem mem_isometryGroup
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : M ≃ₘ^∞⟮I, I⟯ M) :
    φ ∈ isometryGroup g ↔ IsIsometryDiffeomorph g g φ :=
  Iff.rfl

/-- Membership in the conformal group is the conformality predicate. -/
@[simp]
theorem mem_conformalGroup
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : M ≃ₘ^∞⟮I, I⟯ M) :
    φ ∈ conformalGroup g ↔ IsConformalDiffeomorph g g φ :=
  Iff.rfl

/-- Every isometry is a conformal transformation. -/
theorem isometryGroup_le_conformalGroup
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    isometryGroup g ≤ conformalGroup g := by
  intro φ hφ
  have hφ' : IsIsometryDiffeomorph g g φ := (mem_isometryGroup g φ).mp hφ
  exact hφ'.isConformalDiffeomorph

end Groups

section Invariance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Conformal transformations depend only on the conformal class. -/
theorem conformalGroup_eq_of_mem_conformalClass
    {g g' : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hmem : g' ∈ conformalClass g) :
    conformalGroup g' = conformalGroup g := by
  obtain ⟨v, hv, hpos, hvv⟩ := hmem
  have hv_ne : ∀ x, v x ≠ 0 := fun x ↦ ne_of_gt (hpos x)
  have h_inv : ∀ x (a b : TangentSpace I x),
      g.inner x a b = (v x)⁻¹ * g'.inner x a b := by
    intro x a b
    rw [hvv x a b, ← mul_assoc, inv_mul_cancel₀ (hv_ne x), one_mul]
  apply Subgroup.ext
  intro φ
  simp only [mem_conformalGroup]
  constructor
  · intro hconf
    obtain ⟨u', hu', hupos, hueq'⟩ := hconf
    have hvφ_inv : ContMDiff I 𝓘(ℝ) ∞ (fun x ↦ (v (φ x))⁻¹) :=
      (hv.comp φ.contMDiff).inv₀ (fun x ↦ hv_ne (φ x))
    have hu_new : ContMDiff I 𝓘(ℝ) ∞ (fun x ↦ (v (φ x))⁻¹ * u' x * v x) :=
      (hvφ_inv.mul hu').mul hv
    have hpos_new : ∀ x, 0 < (v (φ x))⁻¹ * u' x * v x :=
      fun x ↦ mul_pos (mul_pos (inv_pos.mpr (hpos (φ x))) (hupos x)) (hpos x)
    refine ⟨_, hu_new, hpos_new, ?_⟩
    intro x a b
    have f1 := h_inv (φ x) (mfderiv I I ⇑φ x a) (mfderiv I I ⇑φ x b)
    have f2 := hueq' x a b
    have f3 := hvv x a b
    rw [f1, f2, f3]
    ring
  · intro hconf
    obtain ⟨u, hu, hupos, hueq⟩ := hconf
    have hv_comp : ContMDiff I 𝓘(ℝ) ∞ (v ∘ ⇑φ) := hv.comp φ.contMDiff
    have hv_inv : ContMDiff I 𝓘(ℝ) ∞ (fun x ↦ (v x)⁻¹) := hv.inv₀ (fun x ↦ hv_ne x)
    have hu_new : ContMDiff I 𝓘(ℝ) ∞ (fun x ↦ v (φ x) * u x * (v x)⁻¹) :=
      ((hv_comp.mul hu).mul hv_inv)
    have hpos_new : ∀ x, 0 < v (φ x) * u x * (v x)⁻¹ :=
      fun x ↦ mul_pos (mul_pos (hpos (φ x)) (hupos x)) (inv_pos.mpr (hpos x))
    refine ⟨_, hu_new, hpos_new, ?_⟩
    intro x a b
    have e1 := hvv (φ x) (mfderiv I I ⇑φ x a) (mfderiv I I ⇑φ x b)
    have e2 := hueq x a b
    have e3 := hvv x a b
    rw [e1, e2, e3]
    have hx_ne : v x ≠ 0 := hv_ne x
    have hcalc : (v (φ x) * u x * (v x)⁻¹) * (v x * g.inner x a b) =
        v (φ x) * (u x * g.inner x a b) := by
      calc (v (φ x) * u x * (v x)⁻¹) * (v x * g.inner x a b)
          = v (φ x) * u x * (((v x)⁻¹ * v x) * g.inner x a b) := by ring
        _ = v (φ x) * u x * g.inner x a b := by rw [inv_mul_cancel₀ hx_ne, one_mul]
        _ = v (φ x) * (u x * g.inner x a b) := by ring
    exact hcalc.symm

/-- Madani's invariant conformal class: metrics fixed by every map in `G`. -/
def invariantConformalClass
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (G : Set (M ≃ₘ^∞⟮I, I⟯ M)) :
    Set (Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :=
  {g' | g' ∈ conformalClass g ∧ ∀ σ ∈ G, IsIsometryDiffeomorph g' g' σ}

/-- An invariant metric lies in the conformal class. -/
theorem invariantConformalClass_subset_conformalClass
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (G : Set (M ≃ₘ^∞⟮I, I⟯ M)) :
    invariantConformalClass g G ⊆ conformalClass g := by
  intro g' hg'
  exact hg'.1

/-- The metric itself is invariant under its own isometries. -/
theorem self_mem_invariantConformalClass
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (G : Set (M ≃ₘ^∞⟮I, I⟯ M)) (hG : ∀ σ ∈ G, IsIsometryDiffeomorph g g σ) :
    g ∈ invariantConformalClass g G := by
  refine ⟨self_mem_conformalClass, hG⟩

end Invariance

section Bridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The differential of a conformal map is a conformal linear map. -/
theorem isConformalMap_mfderiv_of_mem_conformalGroup
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {φ : M ≃ₘ^∞⟮I, I⟯ M} (hφ : φ ∈ conformalGroup g) (x : M) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩;
    IsConformalMap (mfderiv I I ⇑φ x) := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨u, _, hpos, hueq⟩ := (mem_conformalGroup g φ).mp hφ
  have hinner : ∀ a b : TangentSpace I x,
      inner ℝ (mfderiv I I ⇑φ x a) (mfderiv I I ⇑φ x b) =
        g.inner (φ x) (mfderiv I I ⇑φ x a) (mfderiv I I ⇑φ x b) :=
    fun a b => rfl
  have hself : ∀ a b : TangentSpace I x, inner ℝ a b = g.inner x a b :=
    fun a b => rfl
  change IsConformalMap (mfderiv I I ⇑φ x)
  rw [isConformalMap_iff]
  refine ⟨u x, hpos x, fun a b => ?_⟩
  rw [hinner a b, hself a b]
  exact hueq x a b

end Bridge

end Manifold
