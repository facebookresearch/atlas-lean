/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicEndpointLocalizedRobinConsistency











namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section


theorem isingFiniteWeightedDirichletSolve_add
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (f g : V -> Real) :
    isingFiniteWeightedDirichletSolve G conductance boundary
        hconductance hpositive hhit (f + g) =
      isingFiniteWeightedDirichletSolve G conductance boundary
          hconductance hpositive hhit f +
        isingFiniteWeightedDirichletSolve G conductance boundary
          hconductance hpositive hhit g := by
  apply isingFiniteWeightedDirichletOperator_injective
    G conductance boundary hconductance hpositive hhit
  rw [isingFiniteWeightedDirichletOperator_solve, map_add,
    isingFiniteWeightedDirichletOperator_solve,
    isingFiniteWeightedDirichletOperator_solve]



theorem isingFiniteWeightedDirichletSolve_smul
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (c : Real) (f : V -> Real) :
    isingFiniteWeightedDirichletSolve G conductance boundary
        hconductance hpositive hhit (c • f) =
      c • isingFiniteWeightedDirichletSolve G conductance boundary
        hconductance hpositive hhit f := by
  apply isingFiniteWeightedDirichletOperator_injective
    G conductance boundary hconductance hpositive hhit
  rw [isingFiniteWeightedDirichletOperator_solve, map_smul,
    isingFiniteWeightedDirichletOperator_solve]


theorem isingFiniteWeightedDirichletSolve_sum
    {V I : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (s : Finset I) (f : I -> V -> Real) :
    isingFiniteWeightedDirichletSolve G conductance boundary
        hconductance hpositive hhit (∑ i ∈ s, f i) =
      ∑ i ∈ s,
        isingFiniteWeightedDirichletSolve G conductance boundary
          hconductance hpositive hhit (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      apply isingFiniteWeightedDirichletOperator_injective
        G conductance boundary hconductance hpositive hhit
      simp [isingFiniteWeightedDirichletOperator_solve]
  | @insert a s ha ih =>
      simp only [sum_insert ha]
      rw [isingFiniteWeightedDirichletSolve_add, ih]


theorem isingFiniteWeightedLaplacian_pair_comm
    {V : Type*} [Fintype V]
    (conductance : V -> V -> Real)
    (hsymm : forall x y, conductance x y = conductance y x)
    (f g : V -> Real) :
    (∑ x, f x * isingFiniteWeightedLaplacian conductance g x) =
      ∑ x, g x * isingFiniteWeightedLaplacian conductance f x := by
  classical
  let L : Real := ∑ x, ∑ y,
    f x * conductance x y * (g y - g x)
  let R : Real := ∑ x, ∑ y,
    g x * conductance x y * (f y - f x)
  let E : Real := ∑ x, ∑ y,
    conductance x y * (f y - f x) * (g y - g x)
  have hleft :
      (∑ x, f x * isingFiniteWeightedLaplacian conductance g x) = L := by
    unfold L isingFiniteWeightedLaplacian
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hright :
      (∑ x, g x * isingFiniteWeightedLaplacian conductance f x) = R := by
    unfold R isingFiniteWeightedLaplacian
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hswapL : L = ∑ x, ∑ y,
      f y * conductance x y * (g x - g y) := by
    unfold L
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [hsymm]
  have hswapR : R = ∑ x, ∑ y,
      g y * conductance x y * (f x - f y) := by
    unfold R
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [hsymm]
  have henergyL : 2 * L = -E := by
    calc
      2 * L = L + L := by ring
      _ = L + ∑ x, ∑ y,
          f y * conductance x y * (g x - g y) := by rw [hswapL]
      _ = -E := by
        unfold L E
        rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro x _
        rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro y _
        ring
  have henergyR : 2 * R = -E := by
    calc
      2 * R = R + R := by ring
      _ = R + ∑ x, ∑ y,
          g y * conductance x y * (f x - f y) := by rw [hswapR]
      _ = -E := by
        unfold R E
        rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro x _
        rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro y _
        ring
  rw [hleft, hright]
  linarith



theorem isingFiniteGhostConductance_comm
    {V : Type*} (G : SimpleGraph V) (ghostRate : V -> Real)
    (x y : Option V) :
    isingFiniteGhostConductance G ghostRate x y =
      isingFiniteGhostConductance G ghostRate y x := by
  classical
  cases x with
  | none => cases y <;> rfl
  | some x =>
      cases y with
      | none => rfl
      | some y =>
          simp only [isingFiniteGhostConductance]
          rw [G.adj_comm]


noncomputable def isingFiniteWeightedPointPoissonBarrier
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (source : V) : V -> Real := by
  classical
  exact isingFiniteWeightedDirichletSolve G conductance boundary
    hconductance hpositive hhit
    (fun x => if boundary x then 0 else if x = source then -1 else 0)



theorem isingFiniteWeightedSpatialResidualPotential_eq_sum_point
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (residual : V -> Real) :
    isingFiniteWeightedSpatialResidualPotential G conductance boundary
        hconductance hpositive hhit residual =
      ∑ z ∈ (Finset.univ : Finset V),
        residual z • isingFiniteWeightedPointPoissonBarrier
          G conductance boundary hconductance hpositive hhit z := by
  classical
  have hrhs :
      (fun x => if boundary x then (0 : Real) else -residual x) =
        ∑ z ∈ (Finset.univ : Finset V),
          residual z •
            (fun x => if boundary x then (0 : Real) else
              if x = z then -1 else 0) := by
    funext x
    by_cases hx : boundary x
    · simp [hx]
    · simp [hx]
  unfold isingFiniteWeightedSpatialResidualPotential
    isingFiniteWeightedPointPoissonBarrier
  calc
    isingFiniteWeightedDirichletSolve G conductance boundary
        hconductance hpositive hhit
        (fun x => if boundary x then 0 else -residual x) =
      isingFiniteWeightedDirichletSolve G conductance boundary
        hconductance hpositive hhit
        (∑ z ∈ (Finset.univ : Finset V),
          residual z •
            (fun x => if boundary x then (0 : Real) else
              if x = z then -1 else 0)) :=
        congrArg (isingFiniteWeightedDirichletSolve
          G conductance boundary hconductance hpositive hhit) hrhs
    _ = ∑ z ∈ (Finset.univ : Finset V),
        isingFiniteWeightedDirichletSolve G conductance boundary
          hconductance hpositive hhit
          (residual z •
            (fun x => if boundary x then (0 : Real) else
              if x = z then -1 else 0)) :=
      isingFiniteWeightedDirichletSolve_sum G conductance boundary
        hconductance hpositive hhit _ _
    _ = ∑ z ∈ (Finset.univ : Finset V),
        residual z •
          isingFiniteWeightedDirichletSolve G conductance boundary
            hconductance hpositive hhit
            (fun x => if boundary x then (0 : Real) else
              if x = z then -1 else 0) := by
      apply Finset.sum_congr rfl
      intro z _
      exact isingFiniteWeightedDirichletSolve_smul
        G conductance boundary hconductance hpositive hhit _ _


theorem isingFiniteWeightedSpatialResidualPotential_le_sum_point_bound
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (residual bound : V -> Real) (x : V)
    (hresidual : forall z, 0 <= residual z)
    (hbound : forall z,
      isingFiniteWeightedPointPoissonBarrier G conductance boundary
        hconductance hpositive hhit z x <= bound z) :
    isingFiniteWeightedSpatialResidualPotential G conductance boundary
        hconductance hpositive hhit residual x <=
      ∑ z ∈ (Finset.univ : Finset V), residual z * bound z := by
  rw [congrFun (isingFiniteWeightedSpatialResidualPotential_eq_sum_point
    G conductance boundary hconductance hpositive hhit residual) x]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_le_sum
  intro z _
  exact mul_le_mul_of_nonneg_left (hbound z) (hresidual z)


noncomputable def isingFiniteWeightedInteriorExceptionalSources
    {V : Type*} [Fintype V]
    (boundary exceptional : V -> Prop) : Finset V := by
  classical
  exact univ.filter fun z => ¬ boundary z ∧ exceptional z

theorem isingFiniteWeightedPointPoissonBarrier_eq_localized
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (source : V) :
    isingFiniteWeightedPointPoissonBarrier G conductance boundary
        hconductance hpositive hhit source =
      isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
        (fun x => x = source) hconductance hpositive hhit := by
  rfl

theorem isingFiniteWeightedPointPoissonBarrier_boundary
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (source x : V) (hx : boundary x) :
    isingFiniteWeightedPointPoissonBarrier G conductance boundary
      hconductance hpositive hhit source x = 0 := by
  rw [isingFiniteWeightedPointPoissonBarrier_eq_localized]
  exact isingFiniteWeightedLocalizedPoissonBarrier_boundary
    G conductance boundary (fun y => y = source)
    hconductance hpositive hhit x hx

theorem isingFiniteWeightedPointPoissonBarrier_laplacian_source
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (source : V) (hsource : Not (boundary source)) :
    isingFiniteWeightedLaplacian conductance
      (isingFiniteWeightedPointPoissonBarrier G conductance boundary
        hconductance hpositive hhit source) source = -1 := by
  rw [isingFiniteWeightedPointPoissonBarrier_eq_localized]
  exact isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_mem
    G conductance boundary (fun y => y = source)
    hconductance hpositive hhit source hsource rfl

theorem isingFiniteWeightedPointPoissonBarrier_laplacian_off_source
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (source x : V) (hx : Not (boundary x)) (hxs : x ≠ source) :
    isingFiniteWeightedLaplacian conductance
      (isingFiniteWeightedPointPoissonBarrier G conductance boundary
        hconductance hpositive hhit source) x = 0 := by
  rw [isingFiniteWeightedPointPoissonBarrier_eq_localized]
  exact isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_not_mem
    G conductance boundary (fun y => y = source)
    hconductance hpositive hhit x hx hxs

theorem isingFiniteWeightedPointPoissonBarrier_nonneg
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (source : V) :
    forall x, 0 <= isingFiniteWeightedPointPoissonBarrier
      G conductance boundary hconductance hpositive hhit source x := by
  rw [isingFiniteWeightedPointPoissonBarrier_eq_localized]
  exact isingFiniteWeightedLocalizedPoissonBarrier_nonneg
    G conductance boundary (fun y => y = source)
    hconductance hpositive hhit


theorem isingFiniteWeightedPointPoissonBarrier_comm
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (hsymm : forall x y, conductance x y = conductance y x)
    (a b : V) (ha : Not (boundary a)) (hb : Not (boundary b)) :
    isingFiniteWeightedPointPoissonBarrier G conductance boundary
        hconductance hpositive hhit a b =
      isingFiniteWeightedPointPoissonBarrier G conductance boundary
        hconductance hpositive hhit b a := by
  classical
  let Pa := isingFiniteWeightedPointPoissonBarrier G conductance boundary
    hconductance hpositive hhit a
  let Pb := isingFiniteWeightedPointPoissonBarrier G conductance boundary
    hconductance hpositive hhit b
  have hpair := isingFiniteWeightedLaplacian_pair_comm
    conductance hsymm Pa Pb
  have hleft :
      (∑ x, Pa x * isingFiniteWeightedLaplacian conductance Pb x) =
        -Pa b := by
    calc
      _ = ∑ x, if x = b then -Pa x else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hxb : boundary x
        · have hPa : Pa x = 0 := by
            exact isingFiniteWeightedPointPoissonBarrier_boundary
              G conductance boundary hconductance hpositive hhit a x hxb
          by_cases hEq : x = b
          · subst x
            exact False.elim (hb hxb)
          · simp [hPa, hEq]
        · by_cases hEq : x = b
          · subst x
            rw [isingFiniteWeightedPointPoissonBarrier_laplacian_source
              G conductance boundary hconductance hpositive hhit b hb]
            simp
          · rw [isingFiniteWeightedPointPoissonBarrier_laplacian_off_source
              G conductance boundary hconductance hpositive hhit b x hxb hEq]
            simp [hEq]
      _ = -Pa b := by simp
  have hright :
      (∑ x, Pb x * isingFiniteWeightedLaplacian conductance Pa x) =
        -Pb a := by
    calc
      _ = ∑ x, if x = a then -Pb x else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hxa : boundary x
        · have hPb : Pb x = 0 := by
            exact isingFiniteWeightedPointPoissonBarrier_boundary
              G conductance boundary hconductance hpositive hhit b x hxa
          by_cases hEq : x = a
          · subst x
            exact False.elim (ha hxa)
          · simp [hPb, hEq]
        · by_cases hEq : x = a
          · subst x
            rw [isingFiniteWeightedPointPoissonBarrier_laplacian_source
              G conductance boundary hconductance hpositive hhit a ha]
            simp
          · rw [isingFiniteWeightedPointPoissonBarrier_laplacian_off_source
              G conductance boundary hconductance hpositive hhit a x hxa hEq]
            simp [hEq]
      _ = -Pb a := by simp
  rw [hleft, hright] at hpair
  dsimp only [Pa, Pb] at hpair ⊢
  linarith


theorem isingFiniteWeightedPointPoissonBarrier_le_of_superharmonic
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (source : V) (hsource : Not (boundary source)) (barrier : V -> Real)
    (hboundary : forall x, boundary x -> 0 <= barrier x)
    (hsourceLap : isingFiniteWeightedLaplacian conductance barrier source <= -1)
    (hoffLap : forall x, Not (boundary x) -> x ≠ source ->
      isingFiniteWeightedLaplacian conductance barrier x <= 0) :
    forall x, isingFiniteWeightedPointPoissonBarrier
      G conductance boundary hconductance hpositive hhit source x <=
        barrier x := by
  apply isingFiniteWeighted_laplacian_comparison
    G conductance boundary
    (isingFiniteWeightedPointPoissonBarrier G conductance boundary
      hconductance hpositive hhit source)
    barrier hconductance hpositive hhit
  · intro x hx
    rw [isingFiniteWeightedPointPoissonBarrier_boundary
      G conductance boundary hconductance hpositive hhit source x hx]
    exact hboundary x hx
  · intro x hx
    by_cases hxs : x = source
    · subst x
      rw [isingFiniteWeightedPointPoissonBarrier_laplacian_source
        G conductance boundary hconductance hpositive hhit source hsource]
      exact hsourceLap
    · rw [isingFiniteWeightedPointPoissonBarrier_laplacian_off_source
        G conductance boundary hconductance hpositive hhit source x hx hxs]
      exact hoffLap x hx hxs



theorem isingFiniteWeightedLocalizedPoissonBarrier_eq_sum_point
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary exceptional : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b) :
    isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
        exceptional hconductance hpositive hhit =
      ∑ z ∈ isingFiniteWeightedInteriorExceptionalSources boundary exceptional,
        isingFiniteWeightedPointPoissonBarrier G conductance boundary
          hconductance hpositive hhit z := by
  classical
  have hrhs :
      (fun x => if boundary x then (0 : Real) else
        if exceptional x then -1 else 0) =
        ∑ z ∈ isingFiniteWeightedInteriorExceptionalSources boundary exceptional,
          (fun x => if boundary x then (0 : Real) else
            if x = z then -1 else 0) := by
    funext x
    by_cases hxb : boundary x
    · simp [hxb]
    · by_cases hxe : exceptional x
      · simp [isingFiniteWeightedInteriorExceptionalSources, hxb, hxe]
      · simp [isingFiniteWeightedInteriorExceptionalSources, hxb, hxe]
  unfold isingFiniteWeightedLocalizedPoissonBarrier
    isingFiniteWeightedPointPoissonBarrier
  calc
    isingFiniteWeightedDirichletSolve G conductance boundary
        hconductance hpositive hhit
        (fun x => if boundary x then 0 else if exceptional x then -1 else 0) =
      isingFiniteWeightedDirichletSolve G conductance boundary
        hconductance hpositive hhit
        (∑ z ∈ isingFiniteWeightedInteriorExceptionalSources
          boundary exceptional,
          (fun x => if boundary x then 0 else if x = z then -1 else 0)) :=
      congrArg (isingFiniteWeightedDirichletSolve G conductance boundary
        hconductance hpositive hhit) hrhs
    _ = ∑ z ∈ isingFiniteWeightedInteriorExceptionalSources
          boundary exceptional,
        isingFiniteWeightedDirichletSolve G conductance boundary
          hconductance hpositive hhit
          (fun x => if boundary x then 0 else if x = z then -1 else 0) :=
      isingFiniteWeightedDirichletSolve_sum G conductance boundary
        hconductance hpositive hhit _ _



theorem isingFiniteWeightedLocalizedPoissonBarrier_le_card_mul
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary exceptional : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (x : V) (B : Real)
    (hpoint : forall z,
      z ∈ isingFiniteWeightedInteriorExceptionalSources boundary exceptional ->
      isingFiniteWeightedPointPoissonBarrier G conductance boundary
        hconductance hpositive hhit z x <= B) :
    isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
        exceptional hconductance hpositive hhit x <=
      (isingFiniteWeightedInteriorExceptionalSources
        boundary exceptional).card * B := by
  rw [isingFiniteWeightedLocalizedPoissonBarrier_eq_sum_point]
  simp only [Finset.sum_apply]
  calc
    (∑ z ∈ isingFiniteWeightedInteriorExceptionalSources
        boundary exceptional,
      isingFiniteWeightedPointPoissonBarrier G conductance boundary
        hconductance hpositive hhit z x) <=
      ∑ _z ∈ isingFiniteWeightedInteriorExceptionalSources
        boundary exceptional, B := by
          apply Finset.sum_le_sum
          intro z hz
          exact hpoint z hz
    _ = (isingFiniteWeightedInteriorExceptionalSources
          boundary exceptional).card * B := by
      simp



theorem isingFiniteWeightedLocalizedPoissonBarrier_le_card_mul_reciprocal
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary exceptional : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (hsymm : forall x y, conductance x y = conductance y x)
    (x : V) (hx : Not (boundary x)) (B : Real)
    (hpoint : forall z,
      z ∈ isingFiniteWeightedInteriorExceptionalSources boundary exceptional ->
      isingFiniteWeightedPointPoissonBarrier G conductance boundary
        hconductance hpositive hhit x z <= B) :
    isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
        exceptional hconductance hpositive hhit x <=
      (isingFiniteWeightedInteriorExceptionalSources
        boundary exceptional).card * B := by
  apply isingFiniteWeightedLocalizedPoissonBarrier_le_card_mul
    G conductance boundary exceptional hconductance hpositive hhit x B
  intro z hz
  have hz' : Not (boundary z) := by
    have hzpair : Not (boundary z) ∧ exceptional z := by
      simpa [isingFiniteWeightedInteriorExceptionalSources] using hz
    exact hzpair.1
  rw [isingFiniteWeightedPointPoissonBarrier_comm
    G conductance boundary hconductance hpositive hhit hsymm z x hz' hx]
  exact hpoint z hz

namespace FKIsingSquareBoundaryLayerCoordinateOneForm


noncomputable def vertexPointPoissonBarrier
    (n : Nat) (source : Option (FKIsingSquareFullVertexNode n)) :
    Option (FKIsingSquareFullVertexNode n) -> Real :=
  isingFiniteWeightedPointPoissonBarrier
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n)
    (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n) source


noncomputable def facePointPoissonBarrier
    (n : Nat) (source : Option (FKIsingSquareFullFaceNode n)) :
    Option (FKIsingSquareFullFaceNode n) -> Real :=
  isingFiniteWeightedPointPoissonBarrier
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n)
    (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n) source


theorem vertexMarkedEndpointBarrier_eq_sum_point (n radius : Nat) :
    vertexMarkedEndpointBarrier n radius =
      ∑ z ∈ isingFiniteWeightedInteriorExceptionalSources
          (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius),
        isingFiniteWeightedPointPoissonBarrier
          (vertexGhostGraph n) (vertexGhostConductance n)
          (vertexDirichletBoundary n)
          (vertexGhostConductance_nonneg n)
          (vertexGhostConductance_pos_of_adj n)
          (vertexGhost_reaches_boundary n) z := by
  exact isingFiniteWeightedLocalizedPoissonBarrier_eq_sum_point
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius)
    (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n)


theorem faceMarkedEndpointBarrier_eq_sum_point (n radius : Nat) :
    faceMarkedEndpointBarrier n radius =
      ∑ z ∈ isingFiniteWeightedInteriorExceptionalSources
          (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius),
        isingFiniteWeightedPointPoissonBarrier
          (faceGhostGraph n) (faceGhostConductance n)
          (faceDirichletBoundary n)
          (faceGhostConductance_nonneg n)
          (faceGhostConductance_pos_of_adj n)
          (faceGhost_reaches_boundary n) z := by
  exact isingFiniteWeightedLocalizedPoissonBarrier_eq_sum_point
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius)
    (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n)



theorem vertexMarkedEndpointBarrier_le_card_mul_reciprocal
    (n radius : Nat) (x : Option (FKIsingSquareFullVertexNode n))
    (hx : Not (vertexDirichletBoundary n x)) (B : Real)
    (hpoint : forall z,
      z ∈ isingFiniteWeightedInteriorExceptionalSources
        (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius) ->
      vertexPointPoissonBarrier n x z <= B) :
    vertexMarkedEndpointBarrier n radius x <=
      (isingFiniteWeightedInteriorExceptionalSources
        (vertexDirichletBoundary n)
        (vertexMarkedEndpointLayer n radius)).card * B := by
  exact isingFiniteWeightedLocalizedPoissonBarrier_le_card_mul_reciprocal
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius)
    (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n)
    (isingFiniteGhostConductance_comm _ _) x hx B hpoint



theorem faceMarkedEndpointBarrier_le_card_mul_reciprocal
    (n radius : Nat) (x : Option (FKIsingSquareFullFaceNode n))
    (hx : Not (faceDirichletBoundary n x)) (B : Real)
    (hpoint : forall z,
      z ∈ isingFiniteWeightedInteriorExceptionalSources
        (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius) ->
      facePointPoissonBarrier n x z <= B) :
    faceMarkedEndpointBarrier n radius x <=
      (isingFiniteWeightedInteriorExceptionalSources
        (faceDirichletBoundary n)
        (faceMarkedEndpointLayer n radius)).card * B := by
  exact isingFiniteWeightedLocalizedPoissonBarrier_le_card_mul_reciprocal
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius)
    (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n)
    (isingFiniteGhostConductance_comm _ _) x hx B hpoint




theorem PhysicalEndpointLocalizedRobinInputs.primitive_convergence_away_of_pointGreen
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real}
    {radius : Nat -> Nat} {bulkRate layerRate endpointRate : Nat -> Real}
    (H : PhysicalEndpointLocalizedRobinInputs
      N hN Phi mesh radius bulkRate layerRate endpointRate)
    (safe : forall k,
      FKIsingSquareInteriorRadialIncidence (N k) (hN k) -> Prop)
    (vertexGreenBound faceGreenBound mismatchRate : Nat -> Real)
    (hvertexGreen_nonneg : forall k, 0 <= vertexGreenBound k)
    (hfaceGreen_nonneg : forall k, 0 <= faceGreenBound k)
    (hmismatch_nonneg : forall k, 0 <= mismatchRate k)
    (hvertexInterior : forall k e, safe k e ->
      Not (vertexDirichletBoundary (N k)
        (some (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))))
    (hfaceInterior : forall k e, safe k e ->
      Not (faceDirichletBoundary (N k)
        (some (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e))))
    (hvertexGreen : forall k e, safe k e -> forall z,
      z ∈ isingFiniteWeightedInteriorExceptionalSources
        (vertexDirichletBoundary (N k))
        (vertexMarkedEndpointLayer (N k) (radius k)) ->
      vertexPointPoissonBarrier (N k)
        (some (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)) z <=
          vertexGreenBound k)
    (hfaceGreen : forall k e, safe k e -> forall z,
      z ∈ isingFiniteWeightedInteriorExceptionalSources
        (faceDirichletBoundary (N k))
        (faceMarkedEndpointLayer (N k) (radius k)) ->
      facePointPoissonBarrier (N k)
        (some (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e)) z <=
          faceGreenBound k)
    (hmismatch : forall k e, safe k e ->
      |(Phi (fullSquareScaledFaceEmbedding (N k) (mesh k)
          (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e))).im -
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k)
          (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im| <=
        mismatchRate k)
    (hvertexEndpoint_tendsto : Filter.Tendsto
      (fun k => endpointRate k *
        ((isingFiniteWeightedInteriorExceptionalSources
          (vertexDirichletBoundary (N k))
          (vertexMarkedEndpointLayer (N k) (radius k))).card *
            vertexGreenBound k))
      Filter.atTop (nhds 0))
    (hfaceEndpoint_tendsto : Filter.Tendsto
      (fun k => endpointRate k *
        ((isingFiniteWeightedInteriorExceptionalSources
          (faceDirichletBoundary (N k))
          (faceMarkedEndpointLayer (N k) (radius k))).card *
            faceGreenBound k))
      Filter.atTop (nhds 0))
    (hmismatch_tendsto : Filter.Tendsto mismatchRate Filter.atTop (nhds 0)) :
    forall eta : Real, 0 < eta -> ∀ᶠ k in Filter.atTop,
      forall e : FKIsingSquareInteriorRadialIncidence (N k) (hN k),
        safe k e ->
        |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).vertexPrimitive
            (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) -
              (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta /\
          |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).facePrimitive
            (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) -
              (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta := by
  apply H.primitive_convergence_away safe
    (fun k =>
      (isingFiniteWeightedInteriorExceptionalSources
        (vertexDirichletBoundary (N k))
        (vertexMarkedEndpointLayer (N k) (radius k))).card *
          vertexGreenBound k)
    (fun k =>
      (isingFiniteWeightedInteriorExceptionalSources
        (faceDirichletBoundary (N k))
        (faceMarkedEndpointLayer (N k) (radius k))).card *
          faceGreenBound k)
    mismatchRate
  · intro k
    exact mul_nonneg (Nat.cast_nonneg _) (hvertexGreen_nonneg k)
  · intro k
    exact mul_nonneg (Nat.cast_nonneg _) (hfaceGreen_nonneg k)
  · exact hmismatch_nonneg
  · intro k e hsafe
    apply vertexMarkedEndpointBarrier_le_card_mul_reciprocal
    · exact hvertexInterior k e hsafe
    · exact hvertexGreen k e hsafe
  · intro k e hsafe
    apply faceMarkedEndpointBarrier_le_card_mul_reciprocal
    · exact hfaceInterior k e hsafe
    · exact hfaceGreen k e hsafe
  · exact hmismatch
  · exact hvertexEndpoint_tendsto
  · exact hfaceEndpoint_tendsto
  · exact hmismatch_tendsto

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
