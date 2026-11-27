/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor.lean` and
`Definitions/Def_CerednikDrinfeld_FormalUpperHalfPlanePoints.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.AlgebraicGeometry.FormalOmega.DeligneDatum

/-!
# Functoriality of Deligne data

For a Deligne datum `d` over an `𝒪`-algebra `B` we define

* `DeligneDatum.pullback π B g d`, the pullback of `d` along `g ∈ GL₂(K)`, whose line at `M` is
  the preimage of the line of `d` at `g • M`;
* `DeligneDatum.map π f d`, the base change of `d` along an `𝒪`-algebra map `f : B →ₐ[𝒪] B'`,
  whose line at `M` is the `B'`-span of the image of the line of `d` at `M`;
* the chart conditions `DeligneDatum.VertexNondegAt`, `DeligneDatum.EdgeNondegAt`,
  `DeligneDatum.InVertexChart` and `DeligneDatum.InEdgeChart`.

The quotient of the base-changed line is identified with the base change of the quotient through
`quotBaseChange`, the base change of the quotient map composed with the cancellation of base
changes. This avoids unfolding `Module.Grassmannian.baseChangeMkQ`, which is the same map but is
not exposed to importing modules.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open LT.LatticeTree TensorProduct Matrix

namespace CerednikDrinfeld
namespace FormalOmega

section Functoriality

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable (B : Type) [CommRing B] [Algebra 𝒪 B]

/-- Transport between base changes of equal lattices. -/
def transportEquiv {M₁ M₂ : FullLattice 𝒪 K} (h : M₁.1 = M₂.1) :
    latticeBaseChange 𝒪 K B M₁ ≃ₗ[B] latticeBaseChange 𝒪 K B M₂ :=
  (LinearEquiv.ofEq M₁.1 M₂.1 h).baseChange 𝒪 B _ _

theorem transportEquiv_tmul {M₁ M₂ : FullLattice 𝒪 K} (h : M₁.1 = M₂.1) (b : B) (v : ↥M₁.1) :
    transportEquiv B h (b ⊗ₜ v) = b ⊗ₜ (LinearEquiv.ofEq M₁.1 M₂.1 h v) := rfl

variable {B} in
/-- The line of a Deligne datum at equal lattices is transported by `transportEquiv`. -/
theorem DeligneDatum.line_transport (d : DeligneDatum (K := K) π B) {M₁ M₂ : FullLattice 𝒪 K}
    (h : M₁.1 = M₂.1) :
    d.line M₂ = (d.line M₁).map (transportEquiv B h).toLinearMap := by
  obtain ⟨L₁, h₁⟩ := M₁
  obtain ⟨L₂, h₂⟩ := M₂
  change L₁ = L₂ at h
  subst h
  have hT : ∀ x : latticeBaseChange 𝒪 K B ⟨L₁, h₁⟩,
      transportEquiv B (M₁ := ⟨L₁, h₁⟩) (M₂ := ⟨L₁, h₂⟩) rfl x = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul b v => rfl
    | add x y hx hy => rw [LinearEquiv.map_add, hx, hy]
  ext x
  constructor
  · intro hx
    exact ⟨x, hx, hT x⟩
  · rintro ⟨y, hy, rfl⟩
    rw [LinearEquiv.coe_coe, hT y]
    exact hy

theorem actBaseChange_tmul (g : GL (Fin 2) K) (M : FullLattice 𝒪 K) (b : B) (v : ↥M.1) :
    actBaseChange B g M (b ⊗ₜ v) = b ⊗ₜ latticeMapEquiv g M.1 v := rfl

theorem coe_latticeMapEquiv_apply (g : GL (Fin 2) K) (L : Submodule 𝒪 (Fin 2 → K)) (v : ↥L) :
    ((latticeMapEquiv g L v : ↥(latticeMap g L)) : Fin 2 → K) =
      (g : Matrix (Fin 2) (Fin 2) K) *ᵥ (v : Fin 2 → K) :=
  rfl

theorem actBaseChange_inclBaseChange (g : GL (Fin 2) K) {M' M : FullLattice 𝒪 K}
    (h : M'.1 ≤ M.1) (x : latticeBaseChange 𝒪 K B M') :
    (actBaseChange B g M).toLinearMap (inclBaseChange B h x) =
      inclBaseChange B (latticeMap_mono g h) ((actBaseChange B g M').toLinearMap x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [LinearMap.map_add, hx, hy]
  | tmul b v => rfl

variable {B} in
theorem rTensor_inclBaseChange {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    {M' M : FullLattice 𝒪 K} (h : M'.1 ≤ M.1) (x : latticeBaseChange 𝒪 K B M') :
    LinearMap.rTensor (↥M.1) f.toLinearMap (inclBaseChange B h x) =
      inclBaseChange B' h (LinearMap.rTensor (↥M'.1) f.toLinearMap x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [LinearMap.map_add, hx, hy]
  | tmul b v => rfl

variable {B} in
theorem rTensor_actBaseChange {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    (g : GL (Fin 2) K) (M : FullLattice 𝒪 K) (x : latticeBaseChange 𝒪 K B M) :
    LinearMap.rTensor (↥(FullLattice.act g M).1) f.toLinearMap (actBaseChange B g M x) =
      actBaseChange B' g M (LinearMap.rTensor (↥M.1) f.toLinearMap x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [LinearEquiv.map_add, LinearMap.map_add, hx, hy]
  | tmul b v => rfl

theorem act_act_scalarGL (g : GL (Fin 2) K) (c : Kˣ) (M : FullLattice 𝒪 K) :
    (FullLattice.act (scalarGL c) (FullLattice.act g M)).1 =
      (FullLattice.act g (FullLattice.act (scalarGL c) M)).1 := by
  change latticeMap (scalarGL c) (latticeMap g M.1) = latticeMap g (latticeMap (scalarGL c) M.1)
  rw [← latticeMap_mul, scalarGL_mul_comm, latticeMap_mul]

theorem act_act_inv (g : GL (Fin 2) K) (N : FullLattice 𝒪 K) :
    (FullLattice.act g (FullLattice.act g⁻¹ N)).1 = N.1 :=
  latticeMap_latticeMap_inv g N.1

theorem transport_actBaseChange_scalarGL (g : GL (Fin 2) K) (c : Kˣ) (M : FullLattice 𝒪 K)
    (x : latticeBaseChange 𝒪 K B M) :
    transportEquiv B (act_act_scalarGL g c M)
        (actBaseChange B (scalarGL c) (FullLattice.act g M) (actBaseChange B g M x)) =
      actBaseChange B g (FullLattice.act (scalarGL c) M) (actBaseChange B (scalarGL c) M x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [LinearEquiv.map_add, hx, hy]
  | tmul b v =>
    have h1 : transportEquiv B (act_act_scalarGL g c M)
        (actBaseChange B (scalarGL c) (FullLattice.act g M) (actBaseChange B g M (b ⊗ₜ[𝒪] v))) =
        b ⊗ₜ[𝒪] (LinearEquiv.ofEq _ _ (act_act_scalarGL g c M)
          (latticeMapEquiv (scalarGL c) (FullLattice.act g M).1 (latticeMapEquiv g M.1 v))) :=
      rfl
    have h2 : actBaseChange B g (FullLattice.act (scalarGL c) M)
        (actBaseChange B (scalarGL c) M (b ⊗ₜ[𝒪] v)) =
        b ⊗ₜ[𝒪] latticeMapEquiv g (FullLattice.act (scalarGL c) M).1
          (latticeMapEquiv (scalarGL c) M.1 v) := rfl
    rw [h1, h2]
    congr 1
    apply Subtype.ext
    change (scalarGL c : Matrix (Fin 2) (Fin 2) K) *ᵥ ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ
        (v : Fin 2 → K)) = (g : Matrix (Fin 2) (Fin 2) K) *ᵥ
        ((scalarGL c : Matrix (Fin 2) (Fin 2) K) *ᵥ (v : Fin 2 → K))
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      scalarGL_mul_comm]

variable {B} in
theorem DeligneDatum.tmul_mulVec_mem (d : DeligneDatum (K := K) π B) (g : GL (Fin 2) K)
    (N : FullLattice 𝒪 K) (𝔭 : Ideal B) (v : ↥(FullLattice.act g⁻¹ N).1)
    (hv : (1 : B) ⊗ₜ[𝒪] v ∈ (d.line (FullLattice.act g (FullLattice.act g⁻¹ N))).comap
        (actBaseChange B g (FullLattice.act g⁻¹ N)).toLinearMap ⊔
        (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (FullLattice.act g⁻¹ N)))) :
    (1 : B) ⊗ₜ[𝒪] (⟨(g : Matrix (Fin 2) (Fin 2) K) *ᵥ (v : Fin 2 → K),
        (act_act_inv g N).le (mulVec_mem_latticeMap v.2)⟩ : ↥N.1) ∈
      d.line N ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B N)) := by
  set Φ := (actBaseChange B g (FullLattice.act g⁻¹ N)).trans
    (transportEquiv B (act_act_inv g N)) with hΦ
  have key : Φ ((1 : B) ⊗ₜ[𝒪] v) =
      (1 : B) ⊗ₜ[𝒪] (⟨(g : Matrix (Fin 2) (Fin 2) K) *ᵥ (v : Fin 2 → K),
        (act_act_inv g N).le (mulVec_mem_latticeMap v.2)⟩ : ↥N.1) := by
    rw [hΦ]
    rfl
  rw [← key]
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hv
  rw [← hyz, map_add]
  refine Submodule.mem_sup.mpr ⟨Φ y, ?_, Φ z, ?_, rfl⟩
  · rw [DeligneDatum.line_transport π d (act_act_inv g N), hΦ, LinearEquiv.trans_apply]
    exact Submodule.mem_map_of_mem (Submodule.mem_comap.mp hy)
  · refine Submodule.smul_induction_on
      (p := fun z => Φ z ∈ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B N))) hz
      (fun r hr n _ => ?_) (fun x y hx hy => ?_)
    · rw [LinearEquiv.map_smul]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · rw [LinearEquiv.map_add]
      exact Submodule.add_mem _ hx hy

/-- The pullback of a Deligne datum along `g ∈ GL₂(K)`: its line at `M` is the preimage of the
line at `g • M` under `actBaseChange`. -/
def DeligneDatum.pullback (g : GL (Fin 2) K) (d : DeligneDatum (K := K) π B) :
    DeligneDatum (K := K) π B where
  line M := (d.line (FullLattice.act g M)).comap (actBaseChange B g M).toLinearMap
  invertible M := by
    have := d.invertible (FullLattice.act g M)
    exact Module.Invertible.congr
      (Submodule.Quotient.equiv
        ((d.line (FullLattice.act g M)).comap (actBaseChange B g M).toLinearMap)
        (d.line (FullLattice.act g M)) (actBaseChange B g M)
        (Submodule.map_comap_eq_of_surjective (actBaseChange B g M).surjective _)).symm
  mono h := by
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap] at hx
    rw [Submodule.mem_comap, actBaseChange_inclBaseChange]
    exact d.mono (latticeMap_mono g h) (Submodule.mem_map_of_mem hx)
  homothety c M := by
    rw [DeligneDatum.line_transport π d (act_act_scalarGL g c M),
      d.homothety c (FullLattice.act g M)]
    ext x
    simp only [Submodule.mem_comap, Submodule.mem_map, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, hyx⟩
      refine ⟨(actBaseChange B g M).symm y, ?_, ?_⟩
      · rw [LinearEquiv.apply_symm_apply]
        exact hy
      · apply (actBaseChange B g (FullLattice.act (scalarGL c) M)).injective
        rw [← transport_actBaseChange_scalarGL, LinearEquiv.apply_symm_apply]
        exact hyx
    · rintro ⟨w, hw, rfl⟩
      exact ⟨_, ⟨actBaseChange B g M w, hw, rfl⟩, transport_actBaseChange_scalarGL B g c M w⟩
  nondeg 𝔭 h𝔭 := by
    obtain ⟨N', N, hN, hπ, h1, h2⟩ := d.nondeg 𝔭 h𝔭
    refine ⟨FullLattice.act g⁻¹ N', FullLattice.act g⁻¹ N, latticeMap_mono g⁻¹ hN, ?_, ?_, ?_⟩
    · intro v
      obtain ⟨w, hw, hwv⟩ := mem_latticeMap.mp v.2
      rw [← hwv, ← Matrix.mulVec_smul]
      exact mulVec_mem_latticeMap (hπ ⟨w, hw⟩)
    · intro v hv hmem
      refine h1 ⟨(g : Matrix (Fin 2) (Fin 2) K) *ᵥ (v : Fin 2 → K),
        (act_act_inv g N).le (mulVec_mem_latticeMap v.2)⟩ ?_
        (DeligneDatum.tmul_mulVec_mem π d g N 𝔭 v hmem)
      intro hgv
      apply hv
      have h' := mulVec_mem_latticeMap (g := g⁻¹) hgv
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec] at h'
    · intro v' hv' hmem
      refine h2 ⟨(g : Matrix (Fin 2) (Fin 2) K) *ᵥ (v' : Fin 2 → K),
        (act_act_inv g N').le (mulVec_mem_latticeMap v'.2)⟩ ?_
        (DeligneDatum.tmul_mulVec_mem π d g N' 𝔭 v' hmem)
      rintro ⟨w, hw⟩
      apply hv'
      refine ⟨⟨((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (w : Fin 2 → K),
        mulVec_mem_latticeMap w.2⟩, ?_⟩
      change (v' : Fin 2 → K) = algebraMap 𝒪 K π •
        (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (w : Fin 2 → K))
      have hw' : (g : Matrix (Fin 2) (Fin 2) K) *ᵥ (v' : Fin 2 → K) =
          algebraMap 𝒪 K π • (w : Fin 2 → K) := hw
      rw [← Matrix.mulVec_smul, ← hw', Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mulVec]

theorem DeligneDatum.isPullback_pullback (g : GL (Fin 2) K) (d : DeligneDatum (K := K) π B) :
    DeligneDatum.IsPullback (K := K) (π := π) B g d (DeligneDatum.pullback π B g d) :=
  fun _ => rfl

theorem DeligneDatum.pullback_line (g : GL (Fin 2) K) (d : DeligneDatum (K := K) π B)
    (M : FullLattice 𝒪 K) :
    (DeligneDatum.pullback π B g d).line M =
      (d.line (FullLattice.act g M)).comap (actBaseChange B g M).toLinearMap :=
  rfl

section BaseChange

variable {B} {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')

theorem rTensor_one_tmul (M : FullLattice 𝒪 K) (v : ↥M.1) :
    LinearMap.rTensor (↥M.1) f.toLinearMap ((1 : B) ⊗ₜ[𝒪] v) = (1 : B') ⊗ₜ[𝒪] v := by
  rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one]

theorem rTensor_smul_left {C : Type} [CommRing C] [Algebra 𝒪 C] (g : B' →ₐ[𝒪] C)
    (M : FullLattice 𝒪 K) (b' : B') (y : latticeBaseChange 𝒪 K B' M) :
    LinearMap.rTensor (↥M.1) g.toLinearMap (b' • y) =
      g b' • LinearMap.rTensor (↥M.1) g.toLinearMap y := by
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  | tmul b v =>
    rw [smul_tmul', LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, smul_tmul',
      AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, smul_eq_mul, smul_eq_mul, map_mul]

theorem cancelBaseChange_one_tmul [Algebra B B'] [IsScalarTower 𝒪 B B']
    (hf : ∀ b, algebraMap B B' b = f b) (M : FullLattice 𝒪 K) (x : latticeBaseChange 𝒪 K B M) :
    AlgebraTensorModule.cancelBaseChange 𝒪 B B' B' (↥M.1) ((1 : B') ⊗ₜ[B] x) =
      LinearMap.rTensor (↥M.1) f.toLinearMap x := by
  induction x using TensorProduct.inductionOn with
  | tmul b v =>
    rw [AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.rTensor_tmul,
      AlgHom.toLinearMap_apply, Algebra.smul_def, hf, mul_one]
  | add x y hx hy => rw [tmul_add, LinearEquiv.map_add, LinearMap.map_add, hx, hy]

variable (B') in
/-- The base change of the quotient map `N.mkQ` along `B → B'`, precomposed with the cancellation
`B' ⊗[𝒪] M ≃ B' ⊗[B] (B ⊗[𝒪] M)`. It is the map `Module.Grassmannian.baseChangeMkQ B' N`, restated
here so that its definition can be unfolded. -/
def quotBaseChange [Algebra B B'] [IsScalarTower 𝒪 B B'] (M : FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B M)) :
    latticeBaseChange 𝒪 K B' M →ₗ[B'] B' ⊗[B] (latticeBaseChange 𝒪 K B M ⧸ N) :=
  N.mkQ.baseChange B' ∘ₗ
    (AlgebraTensorModule.cancelBaseChange 𝒪 B B' B' (↥M.1)).symm.toLinearMap

theorem quotBaseChange_surjective [Algebra B B'] [IsScalarTower 𝒪 B B'] (M : FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B M)) :
    Function.Surjective (quotBaseChange B' M N) :=
  (LinearMap.baseChange_surjective B' (Submodule.mkQ_surjective _)).comp
    (AlgebraTensorModule.cancelBaseChange 𝒪 B B' B' (↥M.1)).symm.surjective

theorem quotBaseChange_rTensor [Algebra B B'] [IsScalarTower 𝒪 B B']
    (hf : ∀ b, algebraMap B B' b = f b) (M : FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B M)) (x : latticeBaseChange 𝒪 K B M) :
    quotBaseChange B' M N (LinearMap.rTensor (↥M.1) f.toLinearMap x) = (1 : B') ⊗ₜ[B] N.mkQ x := by
  rw [← cancelBaseChange_one_tmul f hf M x, quotBaseChange, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]

theorem lineBaseChange_eq_ker [Algebra B B'] [IsScalarTower 𝒪 B B']
    (hf : ∀ b, algebraMap B B' b = f b) (M : FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B M)) :
    lineBaseChange f M N = LinearMap.ker (quotBaseChange B' M N) := by
  have hker : LinearMap.ker (N.mkQ.baseChange B') = N.baseChange B' := by
    ext x
    have hx : x ∈ LinearMap.ker (LinearMap.lTensor B' N.mkQ) ↔
        x ∈ LinearMap.range (LinearMap.lTensor B' N.subtype) := by
      rw [lTensor_mkQ (Q := B')]
    rw [LinearMap.mem_ker, LinearMap.mem_range] at hx
    rw [LinearMap.mem_ker, LinearMap.baseChange_eq_lTensor, hx, Submodule.baseChange,
      LinearMap.mem_range, LinearMap.baseChange_eq_lTensor]
  rw [quotBaseChange, LinearMap.ker_comp, hker, ← Submodule.map_equiv_eq_comap_symm,
    Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image,
    lineBaseChange]
  congr 1
  refine Set.image_congr fun x _ => ?_
  exact (cancelBaseChange_one_tmul f hf M x).symm

theorem invertible_quotient_lineBaseChange (M : FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B M))
    (hN : Module.Invertible B (latticeBaseChange 𝒪 K B M ⧸ N)) :
    Module.Invertible B' (latticeBaseChange 𝒪 K B' M ⧸ lineBaseChange f M N) := by
  let : Algebra B B' := f.toAlgebra
  have : IsScalarTower 𝒪 B B' := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  exact Module.Invertible.congr
    (((quotBaseChange B' M N).quotKerEquivOfSurjective
      (quotBaseChange_surjective M N)).symm.trans
      (Submodule.quotEquivOfEq _ _ (lineBaseChange_eq_ker f (fun _ => rfl) M N).symm))

theorem exists_linearMap_apply_not_mem {R : Type*} [CommRing R] {Q : Type*} [AddCommGroup Q]
    [Module R Q] [Module.Projective R Q] (I : Ideal R) (q : Q)
    (hq : q ∉ (I • ⊤ : Submodule R Q)) :
    ∃ φ : Q →ₗ[R] R, φ q ∉ I := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hq
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective R Q›
  have hx : q = Finsupp.linearCombination R id (s q) :=
    (congrArg (fun g : Q →ₗ[R] Q => g q) hs).symm
  rw [hx, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  exact Submodule.smul_mem_smul (h ((Finsupp.lapply i).comp s)) Submodule.mem_top

theorem rTensor_not_mem_lineBaseChange_sup (M : FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B M))
    (hN : Module.Invertible B (latticeBaseChange 𝒪 K B M ⧸ N)) (𝔭' : Ideal B') [𝔭'.IsPrime]
    (x : latticeBaseChange 𝒪 K B M)
    (hx : x ∉ N ⊔ (Ideal.comap f 𝔭' • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))) :
    LinearMap.rTensor (↥M.1) f.toLinearMap x ∉
      lineBaseChange f M N ⊔ (𝔭' • ⊤ : Submodule B' (latticeBaseChange 𝒪 K B' M)) := by
  let : Algebra B B' := f.toAlgebra
  have : IsScalarTower 𝒪 B B' := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  have hq : N.mkQ x ∉
      (Ideal.comap f 𝔭' • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M ⧸ N)) := by
    intro hq
    apply hx
    have : x ∈ ((Ideal.comap f 𝔭' • ⊤ :
        Submodule B (latticeBaseChange 𝒪 K B M)).map N.mkQ).comap N.mkQ := by
      rw [Submodule.mem_comap, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
      exact hq
    rwa [Submodule.comap_map_mkQ] at this
  obtain ⟨φ, hφ⟩ := exists_linearMap_apply_not_mem (Ideal.comap f 𝔭') (N.mkQ x) hq
  let ψ : latticeBaseChange 𝒪 K B' M →ₗ[B'] B' :=
    (AlgebraTensorModule.rid B B' B').toLinearMap ∘ₗ (φ.baseChange B') ∘ₗ quotBaseChange B' M N
  have hψx : ψ (LinearMap.rTensor (↥M.1) f.toLinearMap x) = f (φ (N.mkQ x)) := by
    simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [quotBaseChange_rTensor f (fun _ => rfl), LinearMap.baseChange_tmul,
      AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_one]
    rfl
  have hψN : ∀ y ∈ lineBaseChange f M N, ψ y = 0 := by
    intro y hy
    rw [lineBaseChange_eq_ker f (fun _ => rfl) M N, LinearMap.mem_ker] at hy
    simp only [ψ, LinearMap.comp_apply, hy, map_zero]
  have hψ𝔭 : ∀ y ∈ (𝔭' • ⊤ : Submodule B' (latticeBaseChange 𝒪 K B' M)), ψ y ∈ 𝔭' := by
    intro y hy
    refine Submodule.smul_induction_on (p := fun y => ψ y ∈ 𝔭') hy
      (fun r hr n _ => ?_) (fun x y hx hy => ?_)
    · rw [LinearMap.map_smul, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ hr
    · rw [LinearMap.map_add]
      exact Ideal.add_mem _ hx hy
  intro hmem
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
  apply hφ
  rw [Ideal.mem_comap, ← hψx, ← hyz, map_add, hψN y hy, zero_add]
  exact hψ𝔭 z hz

/-- The base change of a Deligne datum along an `𝒪`-algebra map `f : B →ₐ[𝒪] B'`: its line at
`M` is the `B'`-span of the image of the line of `d` at `M`. -/
def DeligneDatum.map (d : DeligneDatum (K := K) π B) : DeligneDatum (K := K) π B' where
  line M := lineBaseChange f M (d.line M)
  invertible M := invertible_quotient_lineBaseChange f M (d.line M) (d.invertible M)
  mono h := by
    rw [lineBaseChange, lineBaseChange, Submodule.map_span, ← Set.image_comp]
    apply Submodule.span_mono
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨inclBaseChange B h x, d.mono h (Submodule.mem_map_of_mem hx),
      rTensor_inclBaseChange f h x⟩
  homothety c M := by
    rw [lineBaseChange, lineBaseChange, Submodule.map_span, ← Set.image_comp, d.homothety c M,
      Submodule.map_coe, ← Set.image_comp]
    congr 1
    apply Set.image_congr
    intro x _
    exact rTensor_actBaseChange f (scalarGL c) M x
  nondeg 𝔭' h𝔭' := by
    obtain ⟨M', M, h, hπ, h1, h2⟩ := d.nondeg (Ideal.comap f 𝔭') (Ideal.IsPrime.comap f)
    refine ⟨M', M, h, hπ, fun v hv => ?_, fun v' hv' => ?_⟩
    · rw [← rTensor_one_tmul f M v]
      exact rTensor_not_mem_lineBaseChange_sup f M (d.line M) (d.invertible M) 𝔭' _ (h1 v hv)
    · rw [← rTensor_one_tmul f M' v']
      exact rTensor_not_mem_lineBaseChange_sup f M' (d.line M') (d.invertible M') 𝔭' _
        (h2 v' hv')

theorem DeligneDatum.map_line (d : DeligneDatum (K := K) π B) (M : FullLattice 𝒪 K) :
    (d.map π f).line M = lineBaseChange f M (d.line M) :=
  rfl

theorem DeligneDatum.isBaseChange_map (d : DeligneDatum (K := K) π B) :
    DeligneDatum.IsBaseChange (K := K) (π := π) f d (d.map π f) :=
  fun _ => rfl

theorem DeligneDatum.map_id (d : DeligneDatum (K := K) π B) :
    d.map π (AlgHom.id 𝒪 B) = d := by
  apply DeligneDatum.ext'
  funext M
  change lineBaseChange (AlgHom.id 𝒪 _) M (d.line M) = d.line M
  rw [lineBaseChange, AlgHom.toLinearMap_id, LinearMap.rTensor_id, LinearMap.id_coe,
    Set.image_id, Submodule.span_eq]

theorem DeligneDatum.map_comp {C : Type} [CommRing C] [Algebra 𝒪 C] (g : B' →ₐ[𝒪] C)
    (d : DeligneDatum (K := K) π B) :
    d.map π (g.comp f) = (d.map π f).map π g := by
  apply DeligneDatum.ext'
  funext M
  change lineBaseChange (g.comp f) M (d.line M) =
    lineBaseChange g M (lineBaseChange f M (d.line M))
  rw [lineBaseChange, lineBaseChange, lineBaseChange, AlgHom.comp_toLinearMap,
    LinearMap.rTensor_comp, LinearMap.coe_comp, Set.image_comp]
  apply le_antisymm
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    induction hy using Submodule.span_induction with
    | mem s hs => exact Submodule.subset_span ⟨s, hs, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul b' a _ ha => rw [rTensor_smul_left]; exact Submodule.smul_mem _ _ ha

theorem DeligneDatum.map_pullback (g : GL (Fin 2) K) (d : DeligneDatum (K := K) π B) :
    (DeligneDatum.pullback π B g d).map π f = DeligneDatum.pullback π B' g (d.map π f) := by
  apply DeligneDatum.ext'
  funext M
  change lineBaseChange f M ((d.line (FullLattice.act g M)).comap
      (actBaseChange B g M).toLinearMap) =
    (lineBaseChange f (FullLattice.act g M) (d.line (FullLattice.act g M))).comap
      (actBaseChange B' g M).toLinearMap
  rw [lineBaseChange, lineBaseChange, Submodule.comap_equiv_eq_map_symm,
    Submodule.comap_equiv_eq_map_symm, Submodule.map_span, Submodule.map_coe, Set.image_image,
    Set.image_image]
  congr 1
  refine Set.image_congr fun y _ => ?_
  apply (actBaseChange B' g M).injective
  rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    ← rTensor_actBaseChange, LinearEquiv.apply_symm_apply]

end BaseChange

end Functoriality

section ChartLoci

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

/-- The vertex nondegeneracy condition of a Deligne datum at a lattice `M` and an ideal `𝔭`:
no primitive vector of `M` lies in the line plus `𝔭` times the module. -/
def DeligneDatum.VertexNondegAt (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B)
    (M : FullLattice 𝒪 K) : Prop :=
  ∀ v : ↥M.1, (¬ ∃ w : ↥M.1, (v : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K)) →
    (1 : B) ⊗ₜ[𝒪] v ∉ d.line M ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))

/-- The edge nondegeneracy condition of a Deligne datum at an edge `π M ⊆ M' ⊆ M` of lattices and
an ideal `𝔭`. -/
def DeligneDatum.EdgeNondegAt (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B)
    (M' M : FullLattice 𝒪 K) : Prop :=
  M'.1 ≤ M.1 ∧ (∀ v : ↥M.1, (algebraMap 𝒪 K π) • (v : Fin 2 → K) ∈ M'.1) ∧
    (∀ v : ↥M.1, (v : Fin 2 → K) ∉ M'.1 →
      (1 : B) ⊗ₜ[𝒪] v ∉ d.line M ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))) ∧
    (∀ v' : ↥M'.1, (¬ ∃ w : ↥M.1, (v' : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K)) →
      (1 : B) ⊗ₜ[𝒪] v' ∉ d.line M' ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M')))

theorem DeligneDatum.exists_edgeNondegAt (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B)
    (h𝔭 : 𝔭.IsPrime) : ∃ M' M : FullLattice 𝒪 K, d.EdgeNondegAt π 𝔭 M' M := by
  obtain ⟨M', M, h, hπ, h1, h2⟩ := d.nondeg 𝔭 h𝔭
  exact ⟨M', M, h, hπ, h1, h2⟩

/-- A Deligne datum lies in the vertex chart of `M` if it is vertex nondegenerate at `M` at every
prime. -/
def DeligneDatum.InVertexChart (d : DeligneDatum (K := K) π B) (M : FullLattice 𝒪 K) : Prop :=
  ∀ 𝔭 : Ideal B, 𝔭.IsPrime → d.VertexNondegAt π 𝔭 M

/-- A Deligne datum lies in the edge chart of `M' ⊆ M` if it is edge nondegenerate there at every
prime. -/
def DeligneDatum.InEdgeChart (d : DeligneDatum (K := K) π B) (M' M : FullLattice 𝒪 K) : Prop :=
  ∀ 𝔭 : Ideal B, 𝔭.IsPrime → d.EdgeNondegAt π 𝔭 M' M

end ChartLoci

variable {𝒪 : Type} [CommRing 𝒪] (K : Type) [Field K] [Algebra 𝒪 K] in
/-- The standard lattice `𝒪²` as a full lattice. -/
def stdFullLattice : FullLattice 𝒪 K := ⟨stdLattice 𝒪 K, isFullLattice_stdLattice⟩

end FormalOmega
end CerednikDrinfeld

end
