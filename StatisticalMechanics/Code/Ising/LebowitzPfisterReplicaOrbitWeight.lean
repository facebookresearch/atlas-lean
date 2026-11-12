/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRepresentatives









open Finset

namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _


theorem lpReplica_factorialPower_pair (X : Real) (a b : Nat) :
    X ^ a / Nat.factorial a * (X ^ b / Nat.factorial b) =
      X ^ (a + b) / Nat.factorial (a + b) *
        (Nat.choose (a + b) a : Real) := by
  have hnat : (a + b).choose a *
      (Nat.factorial a * Nat.factorial b) =
      Nat.factorial (a + b) := by
    have h := Nat.add_choose_mul_factorial_mul_factorial b a
    rw [Nat.add_comm b a] at h
    rw [<- h]
    ring
  have hfac : ((a + b).choose a : Real) *
      (Nat.factorial a * Nat.factorial b) =
      Nat.factorial (a + b) := by
    exact_mod_cast hnat
  have haf : (Nat.factorial a : Real) ≠ 0 := by
    exact_mod_cast a.factorial_ne_zero
  have hbf : (Nat.factorial b : Real) ≠ 0 := by
    exact_mod_cast b.factorial_ne_zero
  have habf : (Nat.factorial (a + b) : Real) ≠ 0 := by
    exact_mod_cast (a + b).factorial_ne_zero
  rw [pow_add]
  field_simp
  rw [<- hfac]
  ring


noncomputable def lpReplicaProfileOrbitBaseWeight
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Real :=
  (∏ e ∈ lpReplicaCurrentEdgeOrbitFixed G sites,
      (beta * lpReplicaCurrentCoupling J hf r e.1) ^ (q e / 2) /
        Nat.factorial (q e / 2)) *
    ∏ e ∈ lpReplicaCurrentEdgeOrbitStrictReps G sites,
      (beta * lpReplicaCurrentCoupling J hf r e.1) ^ q e /
        Nat.factorial (q e)


noncomputable def lpReplicaProfileOrbitMultiplicity
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Nat :=
  ∏ e ∈ lpReplicaCurrentEdgeOrbitStrictReps G sites,
    Nat.choose (q e) (m e)


theorem lpReplicaWeight_eq_orbitMultiplicity_mul_base
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q) :
    weight (lpReplicaCurrentGraph G sites) beta
        (lpReplicaCurrentCoupling J hf r)
        (ofEdgeFun (lpReplicaCurrentGraph G sites) m) =
      (lpReplicaProfileOrbitMultiplicity G sites q m : Real) *
        lpReplicaProfileOrbitBaseWeight G sites beta J hf r q := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let Jr := lpReplicaCurrentCoupling J hf r
  let f : H.edgeFinset -> Real := fun e =>
    (beta * Jr e.1) ^ m e / Nat.factorial (m e)
  have hfixed :
      (∏ e ∈ lpReplicaCurrentEdgeOrbitFixed G sites, f e) =
        ∏ e ∈ lpReplicaCurrentEdgeOrbitFixed G sites,
          (beta * Jr e.1) ^ (q e / 2) /
            Nat.factorial (q e / 2) := by
    apply Finset.prod_congr rfl
    intro e he
    have heq := congrFun hm e
    have hreflect := (mem_lpReplicaCurrentEdgeOrbitFixed G sites e).1 he
    unfold lpReplicaSymmetrizedProfile at heq
    have hmreflect : m (lpReplicaCurrentEdgeReflect G sites e) = m e :=
      congrArg m hreflect.symm
    have heq' : m e + m e = q e := by
      simpa only [hmreflect] using heq
    have hhalf : q e / 2 = m e := by
      omega
    rw [hhalf]
  have hpairs :
      (∏ e ∈ lpReplicaCurrentEdgeOrbitStrictReps G sites,
        (f e * f (lpReplicaCurrentEdgeReflect G sites e))) =
      ∏ e ∈ lpReplicaCurrentEdgeOrbitStrictReps G sites,
        ((beta * Jr e.1) ^ q e / Nat.factorial (q e) *
          (Nat.choose (q e) (m e) : Real)) := by
    apply Finset.prod_congr rfl
    intro e _
    have heq := congrFun hm e
    unfold lpReplicaSymmetrizedProfile at heq
    have hcoupling : Jr (lpReplicaCurrentEdgeReflect G sites e).1 =
        Jr e.1 := by
      change lpReplicaCurrentCoupling J hf r
          (lpReplicaCurrentEdgeReflect G sites e).1 =
        lpReplicaCurrentCoupling J hf r e.1
      rw [lpReplicaCurrentEdgeReflect_val]
      exact lpReplicaCurrentCoupling_reflect J hf r e.1
    unfold f
    rw [hcoupling]
    simpa only [heq] using lpReplica_factorialPower_pair
      (beta * Jr e.1) (m e)
        (m (lpReplicaCurrentEdgeReflect G sites e))
  rw [weight_ofEdgeFun]
  change (∏ e, f e) = _
  rw [lpReplicaCurrentEdge_prod_orbitPairs G sites f,
    hfixed, hpairs]
  unfold lpReplicaProfileOrbitMultiplicity
  unfold lpReplicaProfileOrbitBaseWeight
  rw [Nat.cast_prod]
  rw [Finset.prod_mul_distrib]
  ring

end

end StatMech.Ising
