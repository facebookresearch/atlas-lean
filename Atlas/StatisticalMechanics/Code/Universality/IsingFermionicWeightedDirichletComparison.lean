/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicDirichletComparison










open Finset SimpleGraph

namespace StatMech.Universality

noncomputable section


noncomputable def isingFiniteWeightedLaplacian
    {V : Type*} [Fintype V]
    (conductance : V → V → Real) (f : V → Real) (x : V) : Real := by
  classical
  exact ∑ y, conductance x y * (f y - f x)

def IsingFiniteWeightedSubharmonicOn
    {V : Type*} [Fintype V]
    (conductance : V → V → Real) (boundary : V → Prop)
    (f : V → Real) : Prop :=
  ∀ x, ¬ boundary x → 0 ≤ isingFiniteWeightedLaplacian conductance f x

def IsingFiniteWeightedSuperharmonicOn
    {V : Type*} [Fintype V]
    (conductance : V → V → Real) (boundary : V → Prop)
    (f : V → Real) : Prop :=
  ∀ x, ¬ boundary x → isingFiniteWeightedLaplacian conductance f x ≤ 0

def IsingFiniteWeightedHarmonicOn
    {V : Type*} [Fintype V]
    (conductance : V → V → Real) (boundary : V → Prop)
    (f : V → Real) : Prop :=
  ∀ x, ¬ boundary x → isingFiniteWeightedLaplacian conductance f x = 0

theorem isingFiniteWeightedLaplacian_const
    {V : Type*} [Fintype V]
    (conductance : V → V → Real) (c : Real) (x : V) :
    isingFiniteWeightedLaplacian conductance (fun _ ↦ c) x = 0 := by
  classical
  simp [isingFiniteWeightedLaplacian]




theorem isingFiniteWeighted_laplacian_comparison
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop) (u h : V → Real)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hboundary : ∀ x, boundary x → u x ≤ h x)
    (hlap : ∀ x, ¬ boundary x →
      isingFiniteWeightedLaplacian conductance h x ≤
        isingFiniteWeightedLaplacian conductance u x) :
    ∀ x, u x ≤ h x := by
  classical
  let d : V → Real := fun x ↦ u x - h x
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ d
    Finset.univ_nonempty
  have hmax (x : V) : d x ≤ d m := hm x (Finset.mem_univ x)
  by_contra hnot
  have hnot' : ∃ z, h z < u z := by
    simpa only [not_forall, not_le] using hnot
  obtain ⟨z, hz⟩ := hnot'
  have hmpos : 0 < d m := lt_of_lt_of_le (sub_pos.mpr hz) (hmax z)
  have hstep {x y : V} (hx : d x = d m) (hxy : G.Adj x y) :
      d y = d m := by
    have hxnot : ¬ boundary x := by
      intro hxb
      have hxbnd := hboundary x hxb
      have hdx : d x ≤ 0 := sub_nonpos.mpr hxbnd
      linarith
    have hterm : ∀ w ∈ (Finset.univ : Finset V),
        conductance x w * (d w - d x) ≤ 0 := by
      intro w _
      exact mul_nonpos_of_nonneg_of_nonpos (hconductance x w)
        (sub_nonpos.mpr (by rw [hx]; exact hmax w))
    have hsumle :
        (∑ w, conductance x w * (d w - d x)) ≤ 0 :=
      Finset.sum_nonpos hterm
    have hsumge :
        0 ≤ ∑ w, conductance x w * (d w - d x) := by
      have hxu := hlap x hxnot
      calc
        0 ≤ isingFiniteWeightedLaplacian conductance u x -
            isingFiniteWeightedLaplacian conductance h x := sub_nonneg.mpr hxu
        _ = ∑ w, conductance x w * (d w - d x) := by
          unfold isingFiniteWeightedLaplacian
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro w _
          dsimp only [d]
          ring
    have hsum : (∑ w, conductance x w * (d w - d x)) = 0 :=
      le_antisymm hsumle hsumge
    have hyzero : conductance x y * (d y - d x) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonpos hterm).1 hsum y (Finset.mem_univ y)
    have hdiff : d y - d x = 0 := by
      rcases mul_eq_zero.mp hyzero with hc | hd
      · exact False.elim ((ne_of_gt (hpositive hxy)) hc)
      · exact hd
    linarith
  obtain ⟨b, hb, hmb⟩ := hhit m
  obtain ⟨p⟩ := hmb
  have hwalk : ∀ {x y : V}, G.Walk x y → d x = d m → d y = d m := by
    intro x y q
    induction q with
    | nil => exact fun hx ↦ hx
    | @cons x y z hxy q ih =>
        intro hx
        exact ih (hstep hx hxy)
  have hpath : d b = d m := hwalk p rfl
  have hbnd := hboundary b hb
  have hdb : d b ≤ 0 := sub_nonpos.mpr hbnd
  linarith

theorem isingFiniteWeighted_subharmonic_le_harmonic
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop) (u h : V → Real)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hu : IsingFiniteWeightedSubharmonicOn conductance boundary u)
    (hh : IsingFiniteWeightedHarmonicOn conductance boundary h)
    (hboundary : ∀ x, boundary x → u x ≤ h x) :
    ∀ x, u x ≤ h x := by
  apply isingFiniteWeighted_laplacian_comparison G conductance boundary
    u h hconductance hpositive hhit hboundary
  intro x hx
  rw [hh x hx]
  exact hu x hx

theorem isingFiniteWeighted_harmonic_le_superharmonic
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop) (h u : V → Real)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hh : IsingFiniteWeightedHarmonicOn conductance boundary h)
    (hu : IsingFiniteWeightedSuperharmonicOn conductance boundary u)
    (hboundary : ∀ x, boundary x → h x ≤ u x) :
    ∀ x, h x ≤ u x := by
  apply isingFiniteWeighted_laplacian_comparison G conductance boundary
    h u hconductance hpositive hhit hboundary
  intro x hx
  rw [hh x hx]
  exact hu x hx



theorem isingFiniteWeighted_subharmonic_le_const
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop) (u : V → Real) (c : Real)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hu : IsingFiniteWeightedSubharmonicOn conductance boundary u)
    (hboundary : ∀ x, boundary x → u x ≤ c) :
    ∀ x, u x ≤ c := by
  apply isingFiniteWeighted_subharmonic_le_harmonic G conductance boundary
    u (fun _ ↦ c) hconductance hpositive hhit hu
  · intro x hx
    exact isingFiniteWeightedLaplacian_const conductance c x
  · exact hboundary


theorem isingFiniteWeighted_const_le_superharmonic
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop) (u : V → Real) (c : Real)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hu : IsingFiniteWeightedSuperharmonicOn conductance boundary u)
    (hboundary : ∀ x, boundary x → c ≤ u x) :
    ∀ x, c ≤ u x := by
  apply isingFiniteWeighted_harmonic_le_superharmonic G conductance boundary
    (fun _ ↦ c) u hconductance hpositive hhit
  · intro x hx
    exact isingFiniteWeightedLaplacian_const conductance c x
  · exact hu
  · exact hboundary


theorem isingFiniteWeightedLaplacian_add
    {V : Type*} [Fintype V]
    (conductance : V → V → Real) (f g : V → Real) (x : V) :
    isingFiniteWeightedLaplacian conductance (fun y ↦ f y + g y) x =
      isingFiniteWeightedLaplacian conductance f x +
        isingFiniteWeightedLaplacian conductance g x := by
  classical
  unfold isingFiniteWeightedLaplacian
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  ring


theorem isingFiniteWeightedLaplacian_const_mul
    {V : Type*} [Fintype V]
    (conductance : V → V → Real) (c : Real) (f : V → Real) (x : V) :
    isingFiniteWeightedLaplacian conductance (fun y ↦ c * f y) x =
      c * isingFiniteWeightedLaplacian conductance f x := by
  classical
  unfold isingFiniteWeightedLaplacian
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring


theorem isingFiniteWeightedLaplacian_add_const
    {V : Type*} [Fintype V]
    (conductance : V → V → Real) (f : V → Real) (c : Real) (x : V) :
    isingFiniteWeightedLaplacian conductance (fun y ↦ f y + c) x =
      isingFiniteWeightedLaplacian conductance f x := by
  rw [isingFiniteWeightedLaplacian_add,
    isingFiniteWeightedLaplacian_const]
  ring


noncomputable def isingFiniteWeightedDirichletOperator
    {V : Type*} [Fintype V]
    (conductance : V → V → Real) (boundary : V → Prop) :
    (V → Real) →ₗ[Real] (V → Real) := by
  classical
  exact
    { toFun := fun f x ↦
        if boundary x then f x else
          isingFiniteWeightedLaplacian conductance f x
      map_add' := by
        intro f g
        funext x
        by_cases hx : boundary x
        · simp [hx]
        · simp only [if_neg hx, Pi.add_apply]
          exact isingFiniteWeightedLaplacian_add conductance f g x
      map_smul' := by
        intro c f
        funext x
        by_cases hx : boundary x
        · simp [hx]
        · simp only [if_neg hx, Pi.smul_apply, smul_eq_mul]
          exact isingFiniteWeightedLaplacian_const_mul conductance c f x }



theorem isingFiniteWeightedDirichletOperator_injective
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) :
    Function.Injective
      (isingFiniteWeightedDirichletOperator conductance boundary) := by
  classical
  intro f g hfg
  have hopzero :
      isingFiniteWeightedDirichletOperator conductance boundary (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  have hboundary : ∀ x, boundary x → (f - g) x = 0 := by
    intro x hx
    have h := congrFun hopzero x
    change (if boundary x then (f - g) x else
      isingFiniteWeightedLaplacian conductance (f - g) x) = 0 at h
    simpa [hx] using h
  have hharmonic :
      IsingFiniteWeightedHarmonicOn conductance boundary (f - g) := by
    intro x hx
    have h := congrFun hopzero x
    change (if boundary x then (f - g) x else
      isingFiniteWeightedLaplacian conductance (f - g) x) = 0 at h
    simpa [hx] using h
  have hle : ∀ x, (f - g) x ≤ 0 := by
    apply isingFiniteWeighted_subharmonic_le_const
      G conductance boundary (f - g) 0 hconductance hpositive hhit
    · intro x hx
      exact (hharmonic x hx).ge
    · intro x hx
      exact (hboundary x hx).le
  have hge : ∀ x, 0 ≤ (f - g) x := by
    apply isingFiniteWeighted_const_le_superharmonic
      G conductance boundary (f - g) 0 hconductance hpositive hhit
    · intro x hx
      exact (hharmonic x hx).le
    · intro x hx
      exact (hboundary x hx).ge
  apply sub_eq_zero.mp
  funext x
  exact le_antisymm (hle x) (hge x)



theorem isingFiniteWeighted_exists_harmonic_extension
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (data : V → Real) :
    ∃ harmonic : V → Real,
      IsingFiniteWeightedHarmonicOn conductance boundary harmonic ∧
        ∀ x, boundary x → harmonic x = data x := by
  classical
  let rhs : V → Real := fun x ↦ if boundary x then data x else 0
  have hsurj : Function.Surjective
      (isingFiniteWeightedDirichletOperator conductance boundary) :=
    LinearMap.injective_iff_surjective.mp
      (isingFiniteWeightedDirichletOperator_injective
        G conductance boundary hconductance hpositive hhit)
  obtain ⟨harmonic, hharmonic⟩ := hsurj rhs
  refine ⟨harmonic, ?_, ?_⟩
  · intro x hx
    have h := congrFun hharmonic x
    change (if boundary x then harmonic x else
      isingFiniteWeightedLaplacian conductance harmonic x) = rhs x at h
    simpa [rhs, hx] using h
  · intro x hx
    have h := congrFun hharmonic x
    change (if boundary x then harmonic x else
      isingFiniteWeightedLaplacian conductance harmonic x) = rhs x at h
    simpa [rhs, hx] using h


noncomputable def isingFiniteWeightedDirichletSolve
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (rhs : V → Real) : V → Real :=
  Classical.choose
    (LinearMap.injective_iff_surjective.mp
      (isingFiniteWeightedDirichletOperator_injective
        G conductance boundary hconductance hpositive hhit) rhs)

theorem isingFiniteWeightedDirichletOperator_solve
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (rhs : V → Real) :
    isingFiniteWeightedDirichletOperator conductance boundary
      (isingFiniteWeightedDirichletSolve G conductance boundary
        hconductance hpositive hhit rhs) = rhs :=
  Classical.choose_spec
    (LinearMap.injective_iff_surjective.mp
      (isingFiniteWeightedDirichletOperator_injective
        G conductance boundary hconductance hpositive hhit) rhs)



noncomputable def isingFiniteWeightedPoissonBarrier
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) : V → Real := by
  classical
  exact isingFiniteWeightedDirichletSolve G conductance boundary
    hconductance hpositive hhit
      (fun x ↦ if boundary x then 0 else -1)

theorem isingFiniteWeightedPoissonBarrier_boundary
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (x : V) (hx : boundary x) :
    isingFiniteWeightedPoissonBarrier G conductance boundary
      hconductance hpositive hhit x = 0 := by
  classical
  have h := congrFun (isingFiniteWeightedDirichletOperator_solve
    G conductance boundary hconductance hpositive hhit
    (fun y ↦ if boundary y then 0 else -1)) x
  change (if boundary x then
      isingFiniteWeightedPoissonBarrier G conductance boundary
        hconductance hpositive hhit x else
      isingFiniteWeightedLaplacian conductance
        (isingFiniteWeightedPoissonBarrier G conductance boundary
          hconductance hpositive hhit) x) =
    (if boundary x then 0 else -1) at h
  simpa [hx] using h

theorem isingFiniteWeightedPoissonBarrier_laplacian
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (x : V) (hx : ¬ boundary x) :
    isingFiniteWeightedLaplacian conductance
      (isingFiniteWeightedPoissonBarrier G conductance boundary
        hconductance hpositive hhit) x = -1 := by
  classical
  have h := congrFun (isingFiniteWeightedDirichletOperator_solve
    G conductance boundary hconductance hpositive hhit
    (fun y ↦ if boundary y then 0 else -1)) x
  change (if boundary x then
      isingFiniteWeightedPoissonBarrier G conductance boundary
        hconductance hpositive hhit x else
      isingFiniteWeightedLaplacian conductance
        (isingFiniteWeightedPoissonBarrier G conductance boundary
          hconductance hpositive hhit) x) =
    (if boundary x then 0 else -1) at h
  simpa [hx] using h

theorem isingFiniteWeightedPoissonBarrier_nonneg
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) :
    ∀ x, 0 ≤ isingFiniteWeightedPoissonBarrier G conductance boundary
      hconductance hpositive hhit x := by
  apply isingFiniteWeighted_const_le_superharmonic
    G conductance boundary
    (isingFiniteWeightedPoissonBarrier G conductance boundary
      hconductance hpositive hhit) 0 hconductance hpositive hhit
  · intro x hx
    rw [isingFiniteWeightedPoissonBarrier_laplacian
      G conductance boundary hconductance hpositive hhit x hx]
    norm_num
  · intro x hx
    rw [isingFiniteWeightedPoissonBarrier_boundary
      G conductance boundary hconductance hpositive hhit x hx]

noncomputable def isingFiniteWeightedPoissonBarrierBound
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) : Real :=
  (Finset.univ.image
    (isingFiniteWeightedPoissonBarrier G conductance boundary
      hconductance hpositive hhit)).max'
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

theorem isingFiniteWeightedPoissonBarrier_le_bound
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (x : V) :
    isingFiniteWeightedPoissonBarrier G conductance boundary
        hconductance hpositive hhit x ≤
      isingFiniteWeightedPoissonBarrierBound G conductance boundary
        hconductance hpositive hhit := by
  classical
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩

theorem isingFiniteWeightedPoissonBarrierBound_nonneg
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) :
    0 ≤ isingFiniteWeightedPoissonBarrierBound G conductance boundary
      hconductance hpositive hhit := by
  let x : V := Classical.choice inferInstance
  exact (isingFiniteWeightedPoissonBarrier_nonneg G conductance boundary
    hconductance hpositive hhit x).trans
      (isingFiniteWeightedPoissonBarrier_le_bound G conductance boundary
        hconductance hpositive hhit x)



theorem isingFiniteWeighted_harmonic_approximation_of_barrier
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop) (harmonic target barrier : V → Real)
    (boundaryError residual barrierBound : Real)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hharmonic : IsingFiniteWeightedHarmonicOn
      conductance boundary harmonic)
    (hboundary : ∀ x, boundary x →
      |harmonic x - target x| ≤ boundaryError)
    (hresidual_nonneg : 0 ≤ residual)
    (hbarrier_nonneg : ∀ x, 0 ≤ barrier x)
    (hbarrier_bound : ∀ x, barrier x ≤ barrierBound)
    (hbarrier_laplacian : ∀ x, ¬ boundary x →
      isingFiniteWeightedLaplacian conductance barrier x ≤ -1)
    (htarget_residual : ∀ x, ¬ boundary x →
      |isingFiniteWeightedLaplacian conductance target x| ≤ residual) :
    ∀ x, |harmonic x - target x| ≤
      boundaryError + residual * barrierBound := by
  let upper : V → Real := fun x ↦
    target x + residual * barrier x + boundaryError
  let lower : V → Real := fun x ↦
    target x + (-residual) * barrier x - boundaryError
  have hupper_super :
      IsingFiniteWeightedSuperharmonicOn conductance boundary upper := by
    intro x hx
    rw [show upper = fun y ↦
        (target y + residual * barrier y) + boundaryError by rfl,
      isingFiniteWeightedLaplacian_add_const,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_const_mul]
    have ht := (abs_le.mp (htarget_residual x hx)).2
    have hb := hbarrier_laplacian x hx
    nlinarith
  have hlower_sub :
      IsingFiniteWeightedSubharmonicOn conductance boundary lower := by
    intro x hx
    rw [show lower = fun y ↦
        (target y + (-residual) * barrier y) + (-boundaryError) by
          funext y
          dsimp only [lower]
          ring,
      isingFiniteWeightedLaplacian_add_const,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_const_mul]
    have ht := (abs_le.mp (htarget_residual x hx)).1
    have hb := hbarrier_laplacian x hx
    nlinarith
  have hupper : ∀ x, harmonic x ≤ upper x := by
    apply isingFiniteWeighted_harmonic_le_superharmonic
      G conductance boundary harmonic upper hconductance hpositive hhit
      hharmonic hupper_super
    intro x hx
    have hb := (abs_le.mp (hboundary x hx)).2
    have hbar := hbarrier_nonneg x
    dsimp only [upper]
    nlinarith
  have hlower : ∀ x, lower x ≤ harmonic x := by
    apply isingFiniteWeighted_subharmonic_le_harmonic
      G conductance boundary lower harmonic hconductance hpositive hhit
      hlower_sub hharmonic
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



theorem isingFiniteWeighted_harmonic_approximation_of_residual
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop) (harmonic target : V → Real)
    (boundaryError residual : Real)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hharmonic : IsingFiniteWeightedHarmonicOn
      conductance boundary harmonic)
    (hboundary : ∀ x, boundary x →
      |harmonic x - target x| ≤ boundaryError)
    (hresidual_nonneg : 0 ≤ residual)
    (htarget_residual : ∀ x, ¬ boundary x →
      |isingFiniteWeightedLaplacian conductance target x| ≤ residual) :
    ∀ x, |harmonic x - target x| ≤ boundaryError + residual *
      isingFiniteWeightedPoissonBarrierBound G conductance boundary
        hconductance hpositive hhit := by
  apply isingFiniteWeighted_harmonic_approximation_of_barrier
    G conductance boundary harmonic target
    (isingFiniteWeightedPoissonBarrier G conductance boundary
      hconductance hpositive hhit)
    boundaryError residual
    (isingFiniteWeightedPoissonBarrierBound G conductance boundary
      hconductance hpositive hhit)
    hconductance hpositive hhit hharmonic hboundary hresidual_nonneg
    (isingFiniteWeightedPoissonBarrier_nonneg G conductance boundary
      hconductance hpositive hhit)
    (isingFiniteWeightedPoissonBarrier_le_bound G conductance boundary
      hconductance hpositive hhit)
  · intro x hx
    rw [isingFiniteWeightedPoissonBarrier_laplacian
      G conductance boundary hconductance hpositive hhit x hx]
  · exact htarget_residual






noncomputable def isingFiniteWeightedSpatialResidualPotential
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (residual : V → Real) : V → Real := by
  classical
  exact isingFiniteWeightedDirichletSolve G conductance boundary
    hconductance hpositive hhit
      (fun x ↦ if boundary x then 0 else -residual x)

theorem isingFiniteWeightedSpatialResidualPotential_boundary
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (residual : V → Real) (x : V) (hx : boundary x) :
    isingFiniteWeightedSpatialResidualPotential G conductance boundary
      hconductance hpositive hhit residual x = 0 := by
  classical
  have h := congrFun (isingFiniteWeightedDirichletOperator_solve
    G conductance boundary hconductance hpositive hhit
      (fun y ↦ if boundary y then 0 else -residual y)) x
  change (if boundary x then
      isingFiniteWeightedSpatialResidualPotential G conductance boundary
        hconductance hpositive hhit residual x else
      isingFiniteWeightedLaplacian conductance
        (isingFiniteWeightedSpatialResidualPotential G conductance boundary
          hconductance hpositive hhit residual) x) =
    (if boundary x then 0 else -residual x) at h
  simpa [hx] using h

theorem isingFiniteWeightedSpatialResidualPotential_laplacian
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (residual : V → Real) (x : V) (hx : ¬ boundary x) :
    isingFiniteWeightedLaplacian conductance
      (isingFiniteWeightedSpatialResidualPotential G conductance boundary
        hconductance hpositive hhit residual) x = -residual x := by
  classical
  have h := congrFun (isingFiniteWeightedDirichletOperator_solve
    G conductance boundary hconductance hpositive hhit
      (fun y ↦ if boundary y then 0 else -residual y)) x
  change (if boundary x then
      isingFiniteWeightedSpatialResidualPotential G conductance boundary
        hconductance hpositive hhit residual x else
      isingFiniteWeightedLaplacian conductance
        (isingFiniteWeightedSpatialResidualPotential G conductance boundary
          hconductance hpositive hhit residual) x) =
    (if boundary x then 0 else -residual x) at h
  simpa [hx] using h

theorem isingFiniteWeightedSpatialResidualPotential_nonneg
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (residual : V → Real) (hresidual : ∀ x, 0 ≤ residual x) :
    ∀ x, 0 ≤ isingFiniteWeightedSpatialResidualPotential
      G conductance boundary hconductance hpositive hhit residual x := by
  apply isingFiniteWeighted_const_le_superharmonic
    G conductance boundary
    (isingFiniteWeightedSpatialResidualPotential G conductance boundary
      hconductance hpositive hhit residual) 0
    hconductance hpositive hhit
  · intro x hx
    rw [isingFiniteWeightedSpatialResidualPotential_laplacian
      G conductance boundary hconductance hpositive hhit residual x hx]
    exact neg_nonpos.mpr (hresidual x)
  · intro x hx
    rw [isingFiniteWeightedSpatialResidualPotential_boundary
      G conductance boundary hconductance hpositive hhit residual x hx]





theorem isingFiniteWeighted_harmonic_approximation_of_spatial_residual
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop) (harmonic target : V → Real)
    (boundaryError : Real) (residual : V → Real)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hharmonic : IsingFiniteWeightedHarmonicOn
      conductance boundary harmonic)
    (hboundary : ∀ x, boundary x →
      |harmonic x - target x| ≤ boundaryError)
    (hresidual_nonneg : ∀ x, 0 ≤ residual x)
    (htarget_residual : ∀ x, ¬ boundary x →
      |isingFiniteWeightedLaplacian conductance target x| ≤ residual x) :
    ∀ x, |harmonic x - target x| ≤ boundaryError +
      isingFiniteWeightedSpatialResidualPotential G conductance boundary
        hconductance hpositive hhit residual x := by
  let potential := isingFiniteWeightedSpatialResidualPotential
    G conductance boundary hconductance hpositive hhit residual
  let upper : V → Real := fun x ↦ target x + potential x + boundaryError
  let lower : V → Real := fun x ↦ target x - potential x - boundaryError
  have hpotential_nonneg : ∀ x, 0 ≤ potential x :=
    isingFiniteWeightedSpatialResidualPotential_nonneg
      G conductance boundary hconductance hpositive hhit residual
        hresidual_nonneg
  have hupper_super :
      IsingFiniteWeightedSuperharmonicOn conductance boundary upper := by
    intro x hx
    rw [show upper = fun y ↦ (target y + potential y) + boundaryError by rfl,
      isingFiniteWeightedLaplacian_add_const,
      isingFiniteWeightedLaplacian_add]
    have ht := (abs_le.mp (htarget_residual x hx)).2
    have hp := isingFiniteWeightedSpatialResidualPotential_laplacian
      G conductance boundary hconductance hpositive hhit residual x hx
    change isingFiniteWeightedLaplacian conductance potential x =
      -residual x at hp
    linarith
  have hlower_sub :
      IsingFiniteWeightedSubharmonicOn conductance boundary lower := by
    intro x hx
    rw [show lower = fun y ↦
        (target y + (-1) * potential y) + (-boundaryError) by
          funext y
          dsimp only [lower]
          ring,
      isingFiniteWeightedLaplacian_add_const,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_const_mul]
    have ht := (abs_le.mp (htarget_residual x hx)).1
    have hp := isingFiniteWeightedSpatialResidualPotential_laplacian
      G conductance boundary hconductance hpositive hhit residual x hx
    change isingFiniteWeightedLaplacian conductance potential x =
      -residual x at hp
    linarith
  have hupper : ∀ x, harmonic x ≤ upper x := by
    apply isingFiniteWeighted_harmonic_le_superharmonic
      G conductance boundary harmonic upper hconductance hpositive hhit
      hharmonic hupper_super
    intro x hx
    have hb := (abs_le.mp (hboundary x hx)).2
    have hp := isingFiniteWeightedSpatialResidualPotential_boundary
      G conductance boundary hconductance hpositive hhit residual x hx
    change potential x = 0 at hp
    dsimp only [upper]
    linarith
  have hlower : ∀ x, lower x ≤ harmonic x := by
    apply isingFiniteWeighted_subharmonic_le_harmonic
      G conductance boundary lower harmonic hconductance hpositive hhit
      hlower_sub hharmonic
    intro x hx
    have hb := (abs_le.mp (hboundary x hx)).1
    have hp := isingFiniteWeightedSpatialResidualPotential_boundary
      G conductance boundary hconductance hpositive hhit residual x hx
    change potential x = 0 at hp
    dsimp only [lower]
    linarith
  intro x
  rw [abs_le]
  have hup := hupper x
  have hlo := hlower x
  have hp := hpotential_nonneg x
  dsimp only [upper] at hup
  dsimp only [lower] at hlo
  constructor <;> linarith

end

end StatMech.Universality
