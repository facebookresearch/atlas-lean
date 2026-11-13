/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPrimitiveIntegration









open Finset SimpleGraph

namespace StatMech.Universality

noncomputable section



noncomputable def isingFiniteGraphLaplacian
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (f : V → ℝ) (x : V) : ℝ := by
  classical
  exact ∑ y ∈ G.neighborFinset x, (f y - f x)

def IsingFiniteGraphSubharmonicOn
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (boundary : V → Prop) (f : V → ℝ) : Prop :=
  ∀ x, ¬ boundary x → 0 ≤ isingFiniteGraphLaplacian G f x

def IsingFiniteGraphSuperharmonicOn
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (boundary : V → Prop) (f : V → ℝ) : Prop :=
  ∀ x, ¬ boundary x → isingFiniteGraphLaplacian G f x ≤ 0

def IsingFiniteGraphHarmonicOn
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (boundary : V → Prop) (f : V → ℝ) : Prop :=
  ∀ x, ¬ boundary x → isingFiniteGraphLaplacian G f x = 0


theorem isingFiniteGraphLaplacian_add_const
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (f : V → ℝ) (c : ℝ) (x : V) :
    isingFiniteGraphLaplacian G (fun y ↦ f y + c) x =
      isingFiniteGraphLaplacian G f x := by
  classical
  unfold isingFiniteGraphLaplacian
  apply Finset.sum_congr rfl
  intro y hy
  ring


theorem isingFiniteGraphLaplacian_add
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (f g : V → ℝ) (x : V) :
    isingFiniteGraphLaplacian G (fun y ↦ f y + g y) x =
      isingFiniteGraphLaplacian G f x +
        isingFiniteGraphLaplacian G g x := by
  classical
  unfold isingFiniteGraphLaplacian
  simp only []
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  ring


theorem isingFiniteGraphLaplacian_const_mul
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (c : ℝ) (f : V → ℝ) (x : V) :
    isingFiniteGraphLaplacian G (fun y ↦ c * f y) x =
      c * isingFiniteGraphLaplacian G f x := by
  classical
  unfold isingFiniteGraphLaplacian
  simp only []
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  ring



noncomputable def isingFiniteGraphDirichletOperator
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (boundary : V → Prop) :
    (V → ℝ) →ₗ[ℝ] (V → ℝ) := by
  classical
  exact
    { toFun := fun f x ↦
        if boundary x then f x else isingFiniteGraphLaplacian G f x
      map_add' := by
        intro f g
        funext x
        by_cases hx : boundary x
        · simp [hx]
        · simp only [if_neg hx, Pi.add_apply]
          exact isingFiniteGraphLaplacian_add G f g x
      map_smul' := by
        intro c f
        funext x
        by_cases hx : boundary x
        · simp [hx]
        · simp only [if_neg hx, Pi.smul_apply, smul_eq_mul]
          exact isingFiniteGraphLaplacian_const_mul G c f x }


theorem IsingFiniteGraphHarmonicOn.add_const
    {V : Type*} [Fintype V]
    {G : SimpleGraph V} {boundary : V → Prop} {f : V → ℝ}
    (hf : IsingFiniteGraphHarmonicOn G boundary f) (c : ℝ) :
    IsingFiniteGraphHarmonicOn G boundary (fun x ↦ f x + c) := by
  intro x hx
  rw [isingFiniteGraphLaplacian_add_const]
  exact hf x hx



theorem isingFiniteGraph_laplacian_comparison
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (u h : V → ℝ)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hboundary : ∀ x, boundary x → u x ≤ h x)
    (hlap : ∀ x, ¬ boundary x →
      isingFiniteGraphLaplacian G h x ≤
        isingFiniteGraphLaplacian G u x) :
    ∀ x, u x ≤ h x := by
  classical
  let d : V → ℝ := fun x => u x - h x
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ d
    Finset.univ_nonempty
  have hmax (x : V) : d x ≤ d m := hm x (Finset.mem_univ x)
  by_contra hnot
  have hnot' : ∃ z, h z < u z := by
    simpa only [not_forall, not_le] using hnot
  obtain ⟨z, hz⟩ := hnot'
  have hmpos : 0 < d m := lt_of_lt_of_le (sub_pos.mpr hz) (hmax z)
  have hstep {x y : V} (hx : d x = d m) (hxy : G.Adj x y) : d y = d m := by
    have hxnot : ¬ boundary x := by
      intro hxb
      have hxbnd := hboundary x hxb
      have hdx : d x ≤ 0 := sub_nonpos.mpr hxbnd
      linarith
    have hterm : ∀ w ∈ G.neighborFinset x, d w - d x ≤ 0 := by
      intro w hw
      rw [hx]
      exact sub_nonpos.mpr (hmax w)
    have hsumle : (∑ w ∈ G.neighborFinset x, (d w - d x)) ≤ 0 :=
      Finset.sum_nonpos fun w hw => hterm w hw
    have hsumge : 0 ≤ ∑ w ∈ G.neighborFinset x, (d w - d x) := by
      have hxu := hlap x hxnot
      calc
        0 ≤ isingFiniteGraphLaplacian G u x -
            isingFiniteGraphLaplacian G h x := sub_nonneg.mpr hxu
        _ = ∑ w ∈ G.neighborFinset x, (d w - d x) := by
          unfold isingFiniteGraphLaplacian
          rw [← Finset.sum_sub_distrib]
          apply congrArg
            (fun f : V → ℝ => ∑ w ∈ G.neighborFinset x, f w)
          funext w
          dsimp only [d]
          ring
    have hsum : (∑ w ∈ G.neighborFinset x, (d w - d x)) = 0 :=
      le_antisymm hsumle hsumge
    have hyMem : y ∈ G.neighborFinset x := by simpa using hxy
    have hyzero :=
      (Finset.sum_eq_zero_iff_of_nonpos hterm).1 hsum y hyMem
    linarith
  obtain ⟨b, hb, hmb⟩ := hhit m
  obtain ⟨p⟩ := hmb
  have hwalk : ∀ {x y : V}, G.Walk x y → d x = d m → d y = d m := by
    intro x y q
    induction q with
    | nil => exact fun hx => hx
    | @cons x y z hxy q ih =>
        intro hx
        exact ih (hstep hx hxy)
  have hpath : d b = d m := hwalk p rfl
  have hbnd := hboundary b hb
  have hdb : d b ≤ 0 := sub_nonpos.mpr hbnd
  linarith



theorem isingFiniteGraph_subharmonic_le_harmonic
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (u h : V → ℝ)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hu : IsingFiniteGraphSubharmonicOn G boundary u)
    (hh : IsingFiniteGraphHarmonicOn G boundary h)
    (hboundary : ∀ x, boundary x → u x ≤ h x) :
    ∀ x, u x ≤ h x := by
  apply isingFiniteGraph_laplacian_comparison G boundary u h hhit hboundary
  intro x hx
  rw [hh x hx]
  exact hu x hx



theorem isingFiniteGraph_harmonic_le_superharmonic
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (h u : V → ℝ)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hh : IsingFiniteGraphHarmonicOn G boundary h)
    (hu : IsingFiniteGraphSuperharmonicOn G boundary u)
    (hboundary : ∀ x, boundary x → h x ≤ u x) :
    ∀ x, h x ≤ u x := by
  apply isingFiniteGraph_laplacian_comparison G boundary h u hhit hboundary
  intro x hx
  rw [hh x hx]
  exact hu x hx




theorem isingFiniteGraph_harmonic_boundary_stability
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (u v : V → ℝ) (eps : ℝ)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hu : IsingFiniteGraphHarmonicOn G boundary u)
    (hv : IsingFiniteGraphHarmonicOn G boundary v)
    (hboundary : ∀ x, boundary x → |u x - v x| ≤ eps) :
    ∀ x, |u x - v x| ≤ eps := by
  have huv : ∀ x, u x ≤ v x + eps := by
    apply isingFiniteGraph_subharmonic_le_harmonic G boundary u
      (fun x ↦ v x + eps) hhit
    · intro x hx
      rw [hu x hx]
    · exact hv.add_const eps
    · intro x hx
      have hb := hboundary x hx
      rw [abs_le] at hb
      linarith
  have hvu : ∀ x, v x ≤ u x + eps := by
    apply isingFiniteGraph_subharmonic_le_harmonic G boundary v
      (fun x ↦ u x + eps) hhit
    · intro x hx
      rw [hv x hx]
    · exact hu.add_const eps
    · intro x hx
      have hb := hboundary x hx
      rw [abs_le] at hb
      linarith
  intro x
  rw [abs_le]
  constructor <;> linarith [huv x, hvu x]



theorem isingFiniteGraphDirichletOperator_injective
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) :
    Function.Injective (isingFiniteGraphDirichletOperator G boundary) := by
  classical
  intro f g hfg
  have hopzero :
      isingFiniteGraphDirichletOperator G boundary (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  have hboundary : ∀ x, boundary x → (f - g) x = 0 := by
    intro x hx
    have h := congrFun hopzero x
    change (if boundary x then (f - g) x else
      isingFiniteGraphLaplacian G (f - g) x) = 0 at h
    simpa [hx] using h
  have hharmonic :
      IsingFiniteGraphHarmonicOn G boundary (f - g) := by
    intro x hx
    have h := congrFun hopzero x
    change (if boundary x then (f - g) x else
      isingFiniteGraphLaplacian G (f - g) x) = 0 at h
    simpa [hx] using h
  have hzero : IsingFiniteGraphHarmonicOn G boundary (fun _ ↦ 0) := by
    intro x hx
    unfold isingFiniteGraphLaplacian
    simp
  have hstable := isingFiniteGraph_harmonic_boundary_stability
    G boundary (f - g) (fun _ ↦ 0) 0 hhit hharmonic hzero
    (by
      intro x hx
      simp [hboundary x hx])
  apply sub_eq_zero.mp
  funext x
  have hx := hstable x
  simp only [Pi.sub_apply, sub_zero] at hx
  exact abs_eq_zero.mp (le_antisymm hx (abs_nonneg _))



theorem isingFiniteGraph_exists_harmonic_extension
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (data : V → ℝ) :
    ∃ harmonic : V → ℝ,
      IsingFiniteGraphHarmonicOn G boundary harmonic ∧
        ∀ x, boundary x → harmonic x = data x := by
  classical
  let rhs : V → ℝ := fun x ↦ if boundary x then data x else 0
  have hsurj : Function.Surjective
      (isingFiniteGraphDirichletOperator G boundary) :=
    LinearMap.injective_iff_surjective.mp
      (isingFiniteGraphDirichletOperator_injective G boundary hhit)
  obtain ⟨harmonic, hharmonic⟩ := hsurj rhs
  refine ⟨harmonic, ?_, ?_⟩
  · intro x hx
    have h := congrFun hharmonic x
    change (if boundary x then harmonic x else
      isingFiniteGraphLaplacian G harmonic x) = rhs x at h
    simpa [rhs, hx] using h
  · intro x hx
    have h := congrFun hharmonic x
    change (if boundary x then harmonic x else
      isingFiniteGraphLaplacian G harmonic x) = rhs x at h
    simpa [rhs, hx] using h



noncomputable def isingFiniteGraphDirichletSolve
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (rhs : V → ℝ) : V → ℝ :=
  Classical.choose
    (LinearMap.injective_iff_surjective.mp
      (isingFiniteGraphDirichletOperator_injective G boundary hhit) rhs)

theorem isingFiniteGraphDirichletOperator_solve
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (rhs : V → ℝ) :
    isingFiniteGraphDirichletOperator G boundary
      (isingFiniteGraphDirichletSolve G boundary hhit rhs) = rhs :=
  Classical.choose_spec
    (LinearMap.injective_iff_surjective.mp
      (isingFiniteGraphDirichletOperator_injective G boundary hhit) rhs)



noncomputable def isingFiniteGraphPoissonBarrier
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) : V → ℝ := by
  classical
  exact isingFiniteGraphDirichletSolve G boundary hhit
    (fun x ↦ if boundary x then 0 else -1)

theorem isingFiniteGraphPoissonBarrier_boundary
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (x : V) (hx : boundary x) :
    isingFiniteGraphPoissonBarrier G boundary hhit x = 0 := by
  classical
  have h := congrFun
    (isingFiniteGraphDirichletOperator_solve G boundary hhit
      (fun y ↦ if boundary y then 0 else -1)) x
  change (if boundary x then
      isingFiniteGraphPoissonBarrier G boundary hhit x else
      isingFiniteGraphLaplacian G
        (isingFiniteGraphPoissonBarrier G boundary hhit) x) =
    (if boundary x then 0 else -1) at h
  simpa [hx] using h

theorem isingFiniteGraphPoissonBarrier_laplacian
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (x : V) (hx : ¬ boundary x) :
    isingFiniteGraphLaplacian G
      (isingFiniteGraphPoissonBarrier G boundary hhit) x = -1 := by
  classical
  have h := congrFun
    (isingFiniteGraphDirichletOperator_solve G boundary hhit
      (fun y ↦ if boundary y then 0 else -1)) x
  change (if boundary x then
      isingFiniteGraphPoissonBarrier G boundary hhit x else
      isingFiniteGraphLaplacian G
        (isingFiniteGraphPoissonBarrier G boundary hhit) x) =
    (if boundary x then 0 else -1) at h
  simpa [hx] using h

theorem isingFiniteGraphPoissonBarrier_nonneg
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) :
    ∀ x, 0 ≤ isingFiniteGraphPoissonBarrier G boundary hhit x := by
  have hzero : IsingFiniteGraphHarmonicOn G boundary (fun _ ↦ 0) := by
    intro x hx
    unfold isingFiniteGraphLaplacian
    simp
  have hsuper : IsingFiniteGraphSuperharmonicOn G boundary
      (isingFiniteGraphPoissonBarrier G boundary hhit) := by
    intro x hx
    rw [isingFiniteGraphPoissonBarrier_laplacian G boundary hhit x hx]
    norm_num
  apply isingFiniteGraph_harmonic_le_superharmonic
    G boundary (fun _ ↦ 0)
    (isingFiniteGraphPoissonBarrier G boundary hhit)
    hhit hzero hsuper
  intro x hx
  rw [isingFiniteGraphPoissonBarrier_boundary G boundary hhit x hx]


noncomputable def isingFiniteGraphPoissonBarrierBound
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) : ℝ :=
  (Finset.univ.image
    (isingFiniteGraphPoissonBarrier G boundary hhit)).max'
      (Finset.image_nonempty.mpr Finset.univ_nonempty)

theorem isingFiniteGraphPoissonBarrier_le_bound
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (x : V) :
    isingFiniteGraphPoissonBarrier G boundary hhit x ≤
      isingFiniteGraphPoissonBarrierBound G boundary hhit := by
  classical
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩





theorem isingFiniteGraph_subsuperharmonic_boundary_stability
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (u h : V → ℝ) (eps : ℝ)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (husub : IsingFiniteGraphSubharmonicOn G boundary u)
    (husuper : IsingFiniteGraphSuperharmonicOn G boundary u)
    (hh : IsingFiniteGraphHarmonicOn G boundary h)
    (hboundary : ∀ x, boundary x → |u x - h x| ≤ eps) :
    ∀ x, |u x - h x| ≤ eps := by
  have hupper : ∀ x, u x ≤ h x + eps := by
    apply isingFiniteGraph_subharmonic_le_harmonic G boundary u
      (fun x ↦ h x + eps) hhit husub (hh.add_const eps)
    intro x hx
    have hb := hboundary x hx
    rw [abs_le] at hb
    linarith
  have hlower : ∀ x, h x ≤ u x + eps := by
    apply isingFiniteGraph_harmonic_le_superharmonic G boundary h
      (fun x ↦ u x + eps) hhit hh
    · intro x hx
      rw [isingFiniteGraphLaplacian_add_const]
      exact husuper x hx
    · intro x hx
      have hb := hboundary x hx
      rw [abs_le] at hb
      linarith
  intro x
  rw [abs_le]
  constructor <;> linarith [hupper x, hlower x]





theorem isingFiniteGraph_harmonic_approximation_of_barrier
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (harmonic target barrier : V → ℝ)
    (boundaryError residual barrierBound : ℝ)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hharmonic : IsingFiniteGraphHarmonicOn G boundary harmonic)
    (hboundary : ∀ x, boundary x →
      |harmonic x - target x| ≤ boundaryError)
    (hresidual_nonneg : 0 ≤ residual)
    (hbarrier_nonneg : ∀ x, 0 ≤ barrier x)
    (hbarrier_bound : ∀ x, barrier x ≤ barrierBound)
    (hbarrier_laplacian : ∀ x, ¬ boundary x →
      isingFiniteGraphLaplacian G barrier x ≤ -1)
    (htarget_residual : ∀ x, ¬ boundary x →
      |isingFiniteGraphLaplacian G target x| ≤ residual) :
    ∀ x, |harmonic x - target x| ≤
      boundaryError + residual * barrierBound := by
  let upper : V → ℝ := fun x ↦
    target x + residual * barrier x + boundaryError
  let lower : V → ℝ := fun x ↦
    target x + (-residual) * barrier x - boundaryError
  have hupper_super :
      IsingFiniteGraphSuperharmonicOn G boundary upper := by
    intro x hx
    rw [show upper = fun y ↦
        (target y + residual * barrier y) + boundaryError by rfl,
      isingFiniteGraphLaplacian_add_const,
      isingFiniteGraphLaplacian_add,
      isingFiniteGraphLaplacian_const_mul]
    have ht := (abs_le.mp (htarget_residual x hx)).2
    have hb := hbarrier_laplacian x hx
    nlinarith
  have hlower_sub :
      IsingFiniteGraphSubharmonicOn G boundary lower := by
    intro x hx
    rw [show lower = fun y ↦
        (target y + (-residual) * barrier y) + (-boundaryError) by
          funext y
          dsimp only [lower]
          ring,
      isingFiniteGraphLaplacian_add_const,
      isingFiniteGraphLaplacian_add,
      isingFiniteGraphLaplacian_const_mul]
    have ht := (abs_le.mp (htarget_residual x hx)).1
    have hb := hbarrier_laplacian x hx
    nlinarith
  have hupper : ∀ x, harmonic x ≤ upper x := by
    apply isingFiniteGraph_harmonic_le_superharmonic
      G boundary harmonic upper hhit hharmonic hupper_super
    intro x hx
    have hb := (abs_le.mp (hboundary x hx)).2
    have hbar := hbarrier_nonneg x
    dsimp only [upper]
    nlinarith
  have hlower : ∀ x, lower x ≤ harmonic x := by
    apply isingFiniteGraph_subharmonic_le_harmonic
      G boundary lower harmonic hhit hlower_sub hharmonic
    intro x hx
    have hb := (abs_le.mp (hboundary x hx)).1
    have hbar := hbarrier_nonneg x
    dsimp only [lower]
    nlinarith
  intro x
  rw [abs_le]
  have hbar := hbarrier_bound x
  have hup := hupper x
  have hlo := hlower x
  dsimp only [upper] at hup
  dsimp only [lower] at hlo
  constructor <;> nlinarith




theorem isingFiniteGraph_harmonic_approximation_of_residual
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (harmonic target : V → ℝ) (boundaryError residual : ℝ)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hharmonic : IsingFiniteGraphHarmonicOn G boundary harmonic)
    (hboundary : ∀ x, boundary x →
      |harmonic x - target x| ≤ boundaryError)
    (hresidual_nonneg : 0 ≤ residual)
    (htarget_residual : ∀ x, ¬ boundary x →
      |isingFiniteGraphLaplacian G target x| ≤ residual) :
    ∀ x, |harmonic x - target x| ≤ boundaryError + residual *
      isingFiniteGraphPoissonBarrierBound G boundary hhit := by
  apply isingFiniteGraph_harmonic_approximation_of_barrier
    G boundary harmonic target
    (isingFiniteGraphPoissonBarrier G boundary hhit)
    boundaryError residual
    (isingFiniteGraphPoissonBarrierBound G boundary hhit)
    hhit hharmonic hboundary hresidual_nonneg
    (isingFiniteGraphPoissonBarrier_nonneg G boundary hhit)
    (isingFiniteGraphPoissonBarrier_le_bound G boundary hhit)
  · intro x hx
    rw [isingFiniteGraphPoissonBarrier_laplacian G boundary hhit x hx]
  · exact htarget_residual

end

end StatMech.Universality
