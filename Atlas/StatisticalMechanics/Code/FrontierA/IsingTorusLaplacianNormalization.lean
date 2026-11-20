/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingTorusGraph
import Code.FrontierA.IsingTorusExponentialMoment
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix










open Finset Matrix
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


theorem isingTorusGraph_reachable_add_nsmul_step
    (x : IsingDyadicTorus d k) (i : Fin d) (n : Nat) :
    (isingTorusGraph d k).Reachable x
      (x + n • isingTorusStep i) := by
  induction n with
  | zero => simp
  | succ n hn =>
      have hadj : (isingTorusGraph d k).Adj
          (x + n • isingTorusStep i)
          ((x + n • isingTorusStep i) + isingTorusStep i) :=
        ⟨i, Or.inl rfl⟩
      convert hn.trans hadj.reachable using 1
      ext j
      simp only [Pi.add_apply, nsmul_eq_mul,
        Nat.cast_succ, Pi.mul_apply, Pi.one_apply]
      ring



theorem isingTorusGraph_connected :
    (isingTorusGraph d k).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, fun y => ?_⟩
  have hsum (S : Finset (Fin d)) :
      (isingTorusGraph d k).Reachable 0
        (∑ i ∈ S, Pi.single i (y i)) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
        let x : IsingDyadicTorus d k := ∑ j ∈ S, Pi.single j (y j)
        have hcoord :
            (y i).val • (isingTorusStep i : IsingDyadicTorus d k) =
              Pi.single i (y i) := by
          ext j
          by_cases hji : j = i
          · subst j
            simp [isingTorusStep]
          · simp [isingTorusStep, Pi.single_eq_of_ne hji]
        have hstep := isingTorusGraph_reachable_add_nsmul_step
          (d := d) (k := k) x i (y i).val
        rw [hcoord] at hstep
        simpa [x, hi, add_comm] using ih.trans hstep
  simpa [Finset.univ_sum_single] using hsum Finset.univ



def isingTorusIndexedDart
    (p : IsingDyadicTorus d k × Fin d) :
    (isingTorusGraph d k).Dart :=
  ⟨(p.1, p.1 + isingTorusStep p.2), ⟨p.2, Or.inl rfl⟩⟩


def isingTorusOrientedIndexedDart
    (p : (IsingDyadicTorus d k × Fin d) × Bool) :
    (isingTorusGraph d k).Dart :=
  if p.2 then (isingTorusIndexedDart p.1).symm
  else isingTorusIndexedDart p.1

theorem isingTorusOrientedIndexedDart_bijective :
    Function.Bijective
      (isingTorusOrientedIndexedDart (d := d) (k := k)) := by
  constructor
  · rintro ⟨p, b⟩ ⟨q, c⟩ h
    have hedge_oriented
        (r : (IsingDyadicTorus d k × Fin d) × Bool) :
        (isingTorusOrientedIndexedDart r).edge =
          isingTorusIndexedEdge r.1 := by
      unfold isingTorusOrientedIndexedDart
      split <;>
        simp [isingTorusIndexedDart, isingTorusIndexedEdge]
    have hedge : isingTorusIndexedEdge p = isingTorusIndexedEdge q := by
      rw [← hedge_oriented (p, b), h, hedge_oriented]
    have hpq := isingTorusIndexedEdge_injective
      (d := d) (k := k) hedge
    subst q
    cases b <;> cases c
    · rfl
    · have hne := (isingTorusIndexedDart p).symm_ne
      exact (hne h.symm).elim
    · have hne := (isingTorusIndexedDart p).symm_ne
      exact (hne h).elim
    · rfl
  · intro dart
    have hedgeMem : dart.edge ∈ (isingTorusGraph d k).edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset]
      exact dart.edge_mem
    obtain ⟨p, hp⟩ := isingTorusIndexedEdge_surjective
      (d := d) (k := k) ⟨dart.edge, hedgeMem⟩
    have hedge : dart.edge = (isingTorusIndexedDart p).edge := by
      have hp' := congrArg Subtype.val hp
      simpa [isingTorusIndexedDart, isingTorusIndexedEdge] using hp'.symm
    rcases (SimpleGraph.dart_edge_eq_iff dart
      (isingTorusIndexedDart p)).mp hedge with h | h
    · exact ⟨(p, false), by
        simpa [isingTorusOrientedIndexedDart] using h.symm⟩
    · exact ⟨(p, true), by
        simpa [isingTorusOrientedIndexedDart] using h.symm⟩



noncomputable def isingTorusOrientedIndexedDartEquiv :
    ((IsingDyadicTorus d k × Fin d) × Bool) ≃
      (isingTorusGraph d k).Dart :=
  Equiv.ofBijective isingTorusOrientedIndexedDart
    isingTorusOrientedIndexedDart_bijective

private noncomputable def torusDartProdEquiv :
    (isingTorusGraph d k).Dart ≃
      {p : IsingDyadicTorus d k × IsingDyadicTorus d k //
        (isingTorusGraph d k).Adj p.1 p.2} where
  toFun dart := ⟨dart.toProd, dart.adj⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv dart := by ext <;> rfl
  right_inv p := by cases p; rfl



theorem isingTorusDirichlet_eq_lapMatrix_quadratic
    (h : IsingDyadicTorus d k → Real) :
    isingTorusDirichlet h =
      h ⬝ᵥ ((isingTorusGraph d k).lapMatrix Real *ᵥ h) := by
  rw [← Matrix.toLinearMap₂'_apply']
  rw [SimpleGraph.lapMatrix_toLinearMap₂']
  let F : IsingDyadicTorus d k × IsingDyadicTorus d k → Real :=
    fun p => (h p.1 - h p.2) ^ 2
  have hadjSum :
      (∑ x : IsingDyadicTorus d k,
          ∑ y : IsingDyadicTorus d k,
            if (isingTorusGraph d k).Adj x y
            then (h x - h y) ^ 2 else 0) =
        ∑ dart : (isingTorusGraph d k).Dart,
          (h dart.fst - h dart.snd) ^ 2 := by
    calc
      (∑ x : IsingDyadicTorus d k,
          ∑ y : IsingDyadicTorus d k,
            if (isingTorusGraph d k).Adj x y
            then (h x - h y) ^ 2 else 0) =
          ∑ p : IsingDyadicTorus d k × IsingDyadicTorus d k,
            if (isingTorusGraph d k).Adj p.1 p.2 then F p else 0 := by
        exact (Fintype.sum_prod_type (fun p :
          IsingDyadicTorus d k × IsingDyadicTorus d k =>
            if (isingTorusGraph d k).Adj p.1 p.2 then F p else 0)).symm
      _ = (∑ p ∈ Finset.univ.filter
            (fun p => (isingTorusGraph d k).Adj p.1 p.2), F p) := by
        rw [Finset.sum_filter]
      _ = ∑ p : {p : IsingDyadicTorus d k × IsingDyadicTorus d k //
            (isingTorusGraph d k).Adj p.1 p.2}, F p := by
        exact Finset.sum_subtype
          (p := fun p : IsingDyadicTorus d k × IsingDyadicTorus d k =>
            (isingTorusGraph d k).Adj p.1 p.2)
          (s := Finset.univ.filter fun p =>
            (isingTorusGraph d k).Adj p.1 p.2) (by simp) F
      _ = ∑ dart : (isingTorusGraph d k).Dart,
            (h dart.fst - h dart.snd) ^ 2 := by
        rw [← (torusDartProdEquiv (d := d) (k := k)).sum_comp]
        rfl
  have hdartSum :
      (∑ dart : (isingTorusGraph d k).Dart,
          (h dart.fst - h dart.snd) ^ 2) =
        2 * isingTorusDirichlet h := by
    rw [← (isingTorusOrientedIndexedDartEquiv
      (d := d) (k := k)).sum_comp]
    unfold isingTorusDirichlet isingTorusDirichletBilinear
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [isingTorusOrientedIndexedDartEquiv,
      isingTorusOrientedIndexedDart, isingTorusIndexedDart]
    ring
  rw [hadjSum, hdartSum]
  ring



theorem isingTorusDirichletBilinear_eq_lapMatrix
    (u h : IsingDyadicTorus d k → Real) :
    isingTorusDirichletBilinear u h =
      u ⬝ᵥ ((isingTorusGraph d k).lapMatrix Real *ᵥ h) := by
  have hadd := isingTorusDirichlet_add u h
  rw [isingTorusDirichlet_eq_lapMatrix_quadratic,
    isingTorusDirichlet_eq_lapMatrix_quadratic,
    isingTorusDirichlet_eq_lapMatrix_quadratic] at hadd
  have hsymm := (isingTorusGraph d k).isSymm_lapMatrix Real
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct] at hadd
  have hcross :
      h ⬝ᵥ ((isingTorusGraph d k).lapMatrix Real *ᵥ u) =
        u ⬝ᵥ ((isingTorusGraph d k).lapMatrix Real *ᵥ h) := by
    rw [← Matrix.dotProduct_transpose_mulVec]
    rw [hsymm.eq]
  rw [hcross] at hadd
  linarith

private noncomputable def isingTorusSumLinear :
    (IsingDyadicTorus d k → Real) →ₗ[Real] Real where
  toFun f := ∑ x, f x
  map_add' f g := by simp [Finset.sum_add_distrib]
  map_smul' t f := by simp [Finset.mul_sum]



theorem isingTorus_lapMatrix_range_eq_zeroSum :
    LinearMap.range
        (Matrix.toLin' ((isingTorusGraph d k).lapMatrix Real)) =
      LinearMap.ker (isingTorusSumLinear (d := d) (k := k)) := by
  let G := isingTorusGraph d k
  let L := Matrix.toLin' (G.lapMatrix Real)
  let S := isingTorusSumLinear (d := d) (k := k)
  have hle : LinearMap.range L ≤ LinearMap.ker S := by
    rintro _ ⟨h, rfl⟩
    rw [LinearMap.mem_ker]
    change ∑ x, (G.lapMatrix Real *ᵥ h) x = 0
    rw [← one_dotProduct]
    rw [← G.isSymm_lapMatrix Real]
    rw [Matrix.dotProduct_transpose_mulVec]
    have hone := G.lapMatrix_mulVec_const_eq_zero (R := Real)
    change h ⬝ᵥ (G.lapMatrix Real *ᵥ (fun _ => (1 : Real))) = 0
    rw [hone, dotProduct_zero]
  have hconn : G.Connected := isingTorusGraph_connected
  letI : Subsingleton G.ConnectedComponent :=
    hconn.preconnected.subsingleton_connectedComponent
  have hkerL : Module.finrank Real (LinearMap.ker L) = 1 := by
    calc
      Module.finrank Real (LinearMap.ker L) =
          Fintype.card G.ConnectedComponent :=
        (G.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix).symm
      _ = 1 := Fintype.card_eq_one_iff.mpr
        ⟨G.connectedComponentMk 0, fun _ => Subsingleton.elim _ _⟩
  have hSsurj : Function.Surjective S := by
    intro r
    refine ⟨Pi.single (0 : IsingDyadicTorus d k) r, ?_⟩
    simp [S, isingTorusSumLinear]
  have hSrange : LinearMap.range S = ⊤ :=
    LinearMap.range_eq_top.mpr hSsurj
  have hSrangeRank : Module.finrank Real (LinearMap.range S) = 1 := by
    rw [hSrange]
    simp
  have hLdim := L.finrank_range_add_finrank_ker
  have hSdim := S.finrank_range_add_finrank_ker
  rw [hkerL] at hLdim
  rw [hSrangeRank] at hSdim
  apply Submodule.eq_of_le_of_finrank_eq hle
  omega



theorem exists_isingTorusDirichlet_potential
    (f : IsingDyadicTorus d k → Real)
    (hzero : ∑ x, f x = 0) :
    ∃ h : IsingDyadicTorus d k → Real,
      ∀ u : IsingDyadicTorus d k → Real,
        isingTorusDirichletBilinear u h = ∑ x, u x * f x := by
  have hfker : f ∈ LinearMap.ker
      (isingTorusSumLinear (d := d) (k := k)) := by
    simpa [LinearMap.mem_ker, isingTorusSumLinear] using hzero
  rw [← isingTorus_lapMatrix_range_eq_zeroSum] at hfker
  obtain ⟨h, hh⟩ := hfker
  refine ⟨h, fun u => ?_⟩
  rw [isingTorusDirichletBilinear_eq_lapMatrix]
  rw [← Matrix.toLin'_apply, hh]
  rfl



theorem isingTorus_linear_expMoment_le_unconditional
    (beta : Real) (hbeta : 0 < beta)
    (f h : IsingDyadicTorus d k → Real)
    (hpotential : ∀ u : IsingDyadicTorus d k → Real,
      isingTorusDirichletBilinear u h = ∑ x, u x * f x)
    (s : Real) :
    (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) *
        Real.exp (s * ∑ x, isingTorusSpinField sigma x * f x)) /
      isingTorusShiftedPartition (d := d) (k := k) beta 0 ≤
        Real.exp (s ^ 2 * isingTorusDirichlet h / (2 * beta)) := by
  have hmgf := isingTorus_bilinear_expMoment_le_unconditional
    (d := d) (k := k) beta hbeta (-s / beta) h
  simp_rw [hpotential] at hmgf
  convert hmgf using 1 <;> field_simp



theorem isingTorus_linear_expAbsMoment_le_unconditional
    (beta : Real) (hbeta : 0 < beta)
    (f h : IsingDyadicTorus d k → Real)
    (hpotential : ∀ u : IsingDyadicTorus d k → Real,
      isingTorusDirichletBilinear u h = ∑ x, u x * f x)
    (s : Real) :
    (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) *
        Real.exp (s * |∑ x, isingTorusSpinField sigma x * f x|)) /
      isingTorusShiftedPartition (d := d) (k := k) beta 0 ≤
        2 * Real.exp (s ^ 2 * isingTorusDirichlet h / (2 * beta)) := by
  have hmgf := isingTorus_bilinear_expAbsMoment_le_unconditional
    (d := d) (k := k) beta hbeta (s / beta) h
  simp_rw [hpotential] at hmgf
  have hbeta0 : beta ≠ 0 := hbeta.ne'
  convert hmgf using 1
  · apply congrArg (fun z : Real => z / isingTorusShiftedPartition
        (d := d) (k := k) beta 0)
    apply Finset.sum_congr rfl
    intro sigma _
    congr 2
    rw [abs_mul, abs_of_pos hbeta]
    field_simp
  · field_simp



theorem exists_isingTorus_linear_expMoment_bounds
    (beta : Real) (hbeta : 0 < beta)
    (f : IsingDyadicTorus d k → Real)
    (hzero : ∑ x, f x = 0) :
    ∃ h : IsingDyadicTorus d k → Real,
      (∀ u : IsingDyadicTorus d k → Real,
        isingTorusDirichletBilinear u h = ∑ x, u x * f x) ∧
      (∀ s : Real,
        (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
            Real.exp (-(beta / 2) *
              isingTorusDirichlet (isingTorusSpinField sigma)) *
            Real.exp (s * ∑ x,
              isingTorusSpinField sigma x * f x)) /
          isingTorusShiftedPartition (d := d) (k := k) beta 0 ≤
            Real.exp (s ^ 2 * isingTorusDirichlet h / (2 * beta))) ∧
      (∀ s : Real,
        (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
            Real.exp (-(beta / 2) *
              isingTorusDirichlet (isingTorusSpinField sigma)) *
            Real.exp (s * |∑ x,
              isingTorusSpinField sigma x * f x|)) /
          isingTorusShiftedPartition (d := d) (k := k) beta 0 ≤
            2 * Real.exp
              (s ^ 2 * isingTorusDirichlet h / (2 * beta))) := by
  obtain ⟨h, hpotential⟩ := exists_isingTorusDirichlet_potential f hzero
  exact ⟨h, hpotential,
    fun s => isingTorus_linear_expMoment_le_unconditional
      beta hbeta f h hpotential s,
    fun s => isingTorus_linear_expAbsMoment_le_unconditional
      beta hbeta f h hpotential s⟩

end StatMech.FrontierA
