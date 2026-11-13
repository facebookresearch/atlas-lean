/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicDobrushin
import Code.FK.FinitePatternEnergy
















open Finset Complex
open scoped BigOperators

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingDobrushinDomain

theorem fkIsingCriticalParameter_eq_sqrtTwo_mul_one_sub :
    fkIsingCriticalParameter =
      Real.sqrt 2 * (1 - fkIsingCriticalParameter) := by
  unfold fkIsingCriticalParameter selfDualPoint
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  field_simp
  nlinarith

variable {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]
variable (D : FKIsingDobrushinDomain P M)

theorem windingPhase_eq_exp_turn_mul
    (omega omega' : ConfigSpace (Sym2 P.V)) (e e' : M) (turn : Real)
    (h : D.winding omega' e' = D.winding omega e + turn) :
    D.windingPhase omega' e' =
      Complex.exp (Complex.I * ((turn / 2 : Real) : Complex)) *
        D.windingPhase omega e := by
  unfold windingPhase
  rw [h, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem exp_isHalf_turn_pi_div_two_eq_isingLambda :
    Complex.exp (Complex.I * (((Real.pi / 2) / 2 : Real) : Complex)) =
      isingLambda := by
  unfold isingLambda
  congr 1
  push_cast
  ring

theorem exp_isHalf_turn_pi_eq_isingLambda_sq :
    Complex.exp (Complex.I * ((Real.pi / 2 : Real) : Complex)) =
      isingLambda ^ 2 := by
  rw [isingLambda_sq]
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem exp_isHalf_turn_neg_pi_div_two_eq_isingLambda_inv :
    Complex.exp
        (Complex.I * (((-(Real.pi / 2)) / 2 : Real) : Complex)) =
      isingLambda⁻¹ := by
  rw [show ((-(Real.pi / 2)) / 2 : Real) = -(Real.pi / 4) by ring]
  rw [show Complex.I * ((-(Real.pi / 4) : Real) : Complex) =
    -(((Real.pi / 4 : Real) : Complex) * Complex.I) by push_cast; ring]
  rw [Complex.exp_neg]
  rfl



theorem criticalMass_setOpen_eq_sqrtTwo_mul_setClosed_of_clusterCount_eq
    {e : Sym2 P.V} (he : e ∈ P.G.edgeFinset)
    (omega : ConfigSpace (Sym2 P.V))
    (hcluster : numClustersBC P.G D.wiring (setOpen e omega) =
      numClustersBC P.G D.wiring (setClosed e omega)) :
    D.criticalMass (setOpen e omega) =
      Real.sqrt 2 * D.criticalMass (setClosed e omega) := by
  unfold criticalMass bcProb bcWeight
  rw [edgeProduct_setOpen P.G fkIsingCriticalParameter he,
    edgeProduct_setClosed P.G fkIsingCriticalParameter he, hcluster]
  let A := edgeRest P.G fkIsingCriticalParameter e omega *
    2 ^ numClustersBC P.G D.wiring (setClosed e omega) /
      bcZ P.G D.wiring fkIsingCriticalParameter 2
  calc
    edgeRest P.G fkIsingCriticalParameter e omega * fkIsingCriticalParameter *
          2 ^ numClustersBC P.G D.wiring (setClosed e omega) /
        bcZ P.G D.wiring fkIsingCriticalParameter 2 =
      fkIsingCriticalParameter * A := by simp only [A]; ring
    _ = (Real.sqrt 2 * (1 - fkIsingCriticalParameter)) * A :=
      congrArg (fun x : Real => x * A)
        fkIsingCriticalParameter_eq_sqrtTwo_mul_one_sub
    _ = Real.sqrt 2 *
        (edgeRest P.G fkIsingCriticalParameter e omega *
          (1 - fkIsingCriticalParameter) *
          2 ^ numClustersBC P.G D.wiring (setClosed e omega) /
          bcZ P.G D.wiring fkIsingCriticalParameter 2) := by
      simp only [A]
      ring



theorem sqrtTwo_mul_criticalMass_setOpen_eq_setClosed_of_clusterMerge
    {e : Sym2 P.V} (he : e ∈ P.G.edgeFinset)
    (omega : ConfigSpace (Sym2 P.V))
    (hcluster : numClustersBC P.G D.wiring (setClosed e omega) =
      numClustersBC P.G D.wiring (setOpen e omega) + 1) :
    Real.sqrt 2 * D.criticalMass (setOpen e omega) =
      D.criticalMass (setClosed e omega) := by
  unfold criticalMass bcProb bcWeight
  rw [edgeProduct_setOpen P.G fkIsingCriticalParameter he,
    edgeProduct_setClosed P.G fkIsingCriticalParameter he, hcluster, pow_succ]
  let A := edgeRest P.G fkIsingCriticalParameter e omega *
    2 ^ numClustersBC P.G D.wiring (setOpen e omega) /
      bcZ P.G D.wiring fkIsingCriticalParameter 2
  have hp : Real.sqrt 2 * fkIsingCriticalParameter =
      2 * (1 - fkIsingCriticalParameter) := by
    calc
      Real.sqrt 2 * fkIsingCriticalParameter =
          Real.sqrt 2 * (Real.sqrt 2 * (1 - fkIsingCriticalParameter)) :=
        congrArg (fun x : Real => Real.sqrt 2 * x)
          fkIsingCriticalParameter_eq_sqrtTwo_mul_one_sub
      _ = 2 * (1 - fkIsingCriticalParameter) := by
        rw [← mul_assoc, show Real.sqrt 2 * Real.sqrt 2 = 2 by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) <= 2)]]
  calc
    Real.sqrt 2 *
        (edgeRest P.G fkIsingCriticalParameter e omega *
          fkIsingCriticalParameter *
          2 ^ numClustersBC P.G D.wiring (setOpen e omega) /
          bcZ P.G D.wiring fkIsingCriticalParameter 2) =
      (Real.sqrt 2 * fkIsingCriticalParameter) * A := by
        simp only [A]
        ring
    _ = (2 * (1 - fkIsingCriticalParameter)) * A :=
      congrArg (fun x : Real => x * A) hp
    _ = edgeRest P.G fkIsingCriticalParameter e omega *
        (1 - fkIsingCriticalParameter) *
        (2 ^ numClustersBC P.G D.wiring (setOpen e omega) * 2) /
        bcZ P.G D.wiring fkIsingCriticalParameter 2 := by
      simp only [A]
      ring



theorem numClustersBC_setClosed_eq_setOpen_add_one_of_not_reachable
    (a b : P.V) (hab : P.G.Adj a b)
    (omega : ConfigSpace (Sym2 P.V))
    (hnot : ¬(openSub P.G (setClosed s(a, b) omega) ⊔ D.wiring).Reachable a b) :
    numClustersBC P.G D.wiring (setClosed s(a, b) omega) =
      numClustersBC P.G D.wiring (setOpen s(a, b) omega) + 1 := by
  let H := openSub P.G (setClosed s(a, b) omega) ⊔ D.wiring
  have hopen : openSub P.G (setOpen s(a, b) omega) ⊔ D.wiring =
      H ⊔ SimpleGraph.edge a b := by
    ext x y
    simp only [H, SimpleGraph.sup_adj, openSub_adj, SimpleGraph.edge_adj]
    constructor
    · rintro (⟨hxy, hopen⟩ | hC)
      · by_cases hxyab : s(x, y) = s(a, b)
        · rw [Sym2.eq_iff] at hxyab
          rcases hxyab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hab.ne⟩
          · exact Or.inr ⟨Or.inr ⟨rfl, rfl⟩, hab.ne.symm⟩
        · have hopen' := hopen
          rw [setOpen_of_ne hxyab] at hopen'
          rw [setClosed_of_ne hxyab]
          exact Or.inl (Or.inl ⟨hxy, hopen'⟩)
      · exact Or.inl (Or.inr hC)
    · rintro ((⟨hxy, hclosed⟩ | hC) | hedge)
      · exact Or.inl ⟨hxy, by
          by_cases hxyab : s(x, y) = s(a, b)
          · rw [hxyab]
            simp
          · rw [setClosed_of_ne hxyab] at hclosed
            rw [setOpen_of_ne hxyab]
            exact hclosed⟩
      · exact Or.inr hC
      · rcases hedge.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨hab, by simp⟩
        · exact Or.inl ⟨hab.symm, by rw [Sym2.eq_swap]; simp⟩
  have hcount := StatMech.Lattice.card_components_sup_edge_of_not_reachable
    H a b hnot
  unfold numClustersBC
  rw [hopen]
  exact hcount.symm



theorem numClustersBC_setOpen_eq_setClosed_of_reachable
    (a b : P.V) (hab : P.G.Adj a b)
    (omega : ConfigSpace (Sym2 P.V))
    (hreach : (openSub P.G (setClosed s(a, b) omega) ⊔ D.wiring).Reachable a b) :
    numClustersBC P.G D.wiring (setOpen s(a, b) omega) =
      numClustersBC P.G D.wiring (setClosed s(a, b) omega) := by
  let H := openSub P.G (setClosed s(a, b) omega) ⊔ D.wiring
  have hopen : openSub P.G (setOpen s(a, b) omega) ⊔ D.wiring =
      H ⊔ SimpleGraph.edge a b := by
    ext x y
    simp only [H, SimpleGraph.sup_adj, openSub_adj, SimpleGraph.edge_adj]
    constructor
    · rintro (⟨hxy, hopen⟩ | hC)
      · by_cases hxyab : s(x, y) = s(a, b)
        · rw [Sym2.eq_iff] at hxyab
          rcases hxyab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hab.ne⟩
          · exact Or.inr ⟨Or.inr ⟨rfl, rfl⟩, hab.ne.symm⟩
        · have hopen' := hopen
          rw [setOpen_of_ne hxyab] at hopen'
          rw [setClosed_of_ne hxyab]
          exact Or.inl (Or.inl ⟨hxy, hopen'⟩)
      · exact Or.inl (Or.inr hC)
    · rintro ((⟨hxy, hclosed⟩ | hC) | hedge)
      · exact Or.inl ⟨hxy, by
          by_cases hxyab : s(x, y) = s(a, b)
          · rw [hxyab]
            simp
          · rw [setClosed_of_ne hxyab] at hclosed
            rw [setOpen_of_ne hxyab]
            exact hclosed⟩
      · exact Or.inr hC
      · rcases hedge.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨hab, by simp⟩
        · exact Or.inl ⟨hab.symm, by rw [Sym2.eq_swap]; simp⟩
  have hcount := StatMech.Lattice.card_components_sup_edge_of_reachable
    H a b hreach
  unfold numClustersBC
  rw [hopen]
  exact hcount


def localEdgeFlip (e : Sym2 P.V) (omega : ConfigSpace (Sym2 P.V)) :
    ConfigSpace (Sym2 P.V) :=
  Function.update omega e (!(omega e))

theorem localEdgeFlip_involutive (e : Sym2 P.V) :
    Function.Involutive (localEdgeFlip (P := P) e) := by
  intro omega
  funext e'
  by_cases h : e' = e
  · subst e'
    simp [localEdgeFlip]
  · simp [localEdgeFlip, Function.update_of_ne h]



def localEdgeFlipEquiv (e : Sym2 P.V) :
    ConfigSpace (Sym2 P.V) ≃ ConfigSpace (Sym2 P.V) where
  toFun := localEdgeFlip e
  invFun := localEdgeFlip e
  left_inv := localEdgeFlip_involutive e
  right_inv := localEdgeFlip_involutive e

theorem pair_with_localEdgeFlip_eq_closed_add_open
    (e : Sym2 P.V) (f : ConfigSpace (Sym2 P.V) -> Complex)
    (omega : ConfigSpace (Sym2 P.V)) :
    f omega + f (localEdgeFlipEquiv e omega) =
      f (setClosed e omega) + f (setOpen e omega) := by
  cases h : omega e with
  | false =>
      have hclosed : setClosed e omega = omega := by
        funext e'
        by_cases he' : e' = e
        · subst e'
          simp [h]
        · rw [setClosed_of_ne he']
      have hflip : localEdgeFlipEquiv e omega = setOpen e omega := by
        unfold localEdgeFlipEquiv localEdgeFlip setOpen
        simp [h]
      rw [hclosed, hflip]
  | true =>
      have hopen : setOpen e omega = omega := by
        funext e'
        by_cases he' : e' = e
        · subst e'
          simp [h]
        · rw [setOpen_of_ne he']
      have hflip : localEdgeFlipEquiv e omega = setClosed e omega := by
        unfold localEdgeFlipEquiv localEdgeFlip setClosed
        simp [h]
      rw [hopen, hflip, add_comm]




def ClosedOpenPairedBalance (crossingEdge : Sym2 P.V)
    (edges : Fin 4 -> M) : Prop :=
  forall omega,
    (D.fermionicSummand (setClosed crossingEdge omega) (edges 0) +
        D.fermionicSummand (setOpen crossingEdge omega) (edges 0)) -
      (D.fermionicSummand (setClosed crossingEdge omega) (edges 1) +
        D.fermionicSummand (setOpen crossingEdge omega) (edges 1)) =
    Complex.I *
      ((D.fermionicSummand (setClosed crossingEdge omega) (edges 2) +
          D.fermionicSummand (setOpen crossingEdge omega) (edges 2)) -
        (D.fermionicSummand (setClosed crossingEdge omega) (edges 3) +
          D.fermionicSummand (setOpen crossingEdge omega) (edges 3)))





structure CaseTwoExplorationSwitchingLaw where
  crossingA : P.V
  crossingB : P.V
  crossing_adj : P.G.Adj crossingA crossingB
  edges : Fin 4 -> M
  closed_endpoints_not_reachable : forall omega,
    ¬(openSub P.G (setClosed s(crossingA, crossingB) omega) ⊔ D.wiring).Reachable
      crossingA crossingB
  closed_mem_zero : forall omega,
    edges 0 ∈ D.exploration (setClosed s(crossingA, crossingB) omega)
  closed_not_mem_one : forall omega,
    edges 1 ∉ D.exploration (setClosed s(crossingA, crossingB) omega)
  closed_mem_two : forall omega,
    edges 2 ∈ D.exploration (setClosed s(crossingA, crossingB) omega)
  closed_not_mem_three : forall omega,
    edges 3 ∉ D.exploration (setClosed s(crossingA, crossingB) omega)
  open_mem : forall omega k,
    edges k ∈ D.exploration (setOpen s(crossingA, crossingB) omega)
  paired_balance : D.ClosedOpenPairedBalance s(crossingA, crossingB) edges

namespace CaseTwoExplorationSwitchingLaw

variable (L : D.CaseTwoExplorationSwitchingLaw)

def crossingEdge : Sym2 P.V := s(L.crossingA, L.crossingB)

theorem crossingEdge_mem : L.crossingEdge ∈ P.G.edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset]
  exact L.crossing_adj

theorem clusterMerge (omega : ConfigSpace (Sym2 P.V)) :
    numClustersBC P.G D.wiring (setClosed L.crossingEdge omega) =
      numClustersBC P.G D.wiring (setOpen L.crossingEdge omega) + 1 := by
  exact D.numClustersBC_setClosed_eq_setOpen_add_one_of_not_reachable
    L.crossingA L.crossingB L.crossing_adj omega
      (L.closed_endpoints_not_reachable omega)

end CaseTwoExplorationSwitchingLaw




structure CaseThreeExplorationSwitchingLaw where
  crossingA : P.V
  crossingB : P.V
  crossing_adj : P.G.Adj crossingA crossingB
  edges : Fin 4 -> M
  closed_endpoints_reachable : forall omega,
    (openSub P.G (setClosed s(crossingA, crossingB) omega) ⊔ D.wiring).Reachable
      crossingA crossingB
  closed_mem : forall omega k,
    edges k ∈ D.exploration (setClosed s(crossingA, crossingB) omega)
  open_mem_zero : forall omega,
    edges 0 ∈ D.exploration (setOpen s(crossingA, crossingB) omega)
  open_not_mem_one : forall omega,
    edges 1 ∉ D.exploration (setOpen s(crossingA, crossingB) omega)
  open_not_mem_two : forall omega,
    edges 2 ∉ D.exploration (setOpen s(crossingA, crossingB) omega)
  open_mem_three : forall omega,
    edges 3 ∈ D.exploration (setOpen s(crossingA, crossingB) omega)
  paired_balance : D.ClosedOpenPairedBalance
    s(crossingA, crossingB) edges



structure CaseThreeEastSouthExplorationSwitchingLaw where
  crossingA : P.V
  crossingB : P.V
  crossing_adj : P.G.Adj crossingA crossingB
  edges : Fin 4 -> M
  closed_endpoints_reachable : forall omega,
    (openSub P.G (setClosed s(crossingA, crossingB) omega) ⊔ D.wiring).Reachable
      crossingA crossingB
  closed_mem : forall omega k,
    edges k ∈ D.exploration (setClosed s(crossingA, crossingB) omega)
  open_not_mem_zero : forall omega,
    edges 0 ∉ D.exploration (setOpen s(crossingA, crossingB) omega)
  open_mem_one : forall omega,
    edges 1 ∈ D.exploration (setOpen s(crossingA, crossingB) omega)
  open_mem_two : forall omega,
    edges 2 ∈ D.exploration (setOpen s(crossingA, crossingB) omega)
  open_not_mem_three : forall omega,
    edges 3 ∉ D.exploration (setOpen s(crossingA, crossingB) omega)
  paired_balance : D.ClosedOpenPairedBalance
    s(crossingA, crossingB) edges

namespace CaseThreeExplorationSwitchingLaw

variable (L : D.CaseThreeExplorationSwitchingLaw)

def crossingEdge : Sym2 P.V := s(L.crossingA, L.crossingB)

theorem crossingEdge_mem : L.crossingEdge ∈ P.G.edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset]
  exact L.crossing_adj

theorem clusterCountEq (omega : ConfigSpace (Sym2 P.V)) :
    numClustersBC P.G D.wiring (setOpen L.crossingEdge omega) =
      numClustersBC P.G D.wiring (setClosed L.crossingEdge omega) := by
  exact D.numClustersBC_setOpen_eq_setClosed_of_reachable
    L.crossingA L.crossingB L.crossing_adj omega
      (L.closed_endpoints_reachable omega)

end CaseThreeExplorationSwitchingLaw

namespace CaseThreeEastSouthExplorationSwitchingLaw

variable (L : D.CaseThreeEastSouthExplorationSwitchingLaw)

def crossingEdge : Sym2 P.V := s(L.crossingA, L.crossingB)

theorem crossingEdge_mem : L.crossingEdge ∈ P.G.edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset]
  exact L.crossing_adj

theorem clusterCountEq (omega : ConfigSpace (Sym2 P.V)) :
    numClustersBC P.G D.wiring (setOpen L.crossingEdge omega) =
      numClustersBC P.G D.wiring (setClosed L.crossingEdge omega) := by
  exact D.numClustersBC_setOpen_eq_setClosed_of_reachable
    L.crossingA L.crossingB L.crossing_adj omega
      (L.closed_endpoints_reachable omega)

end CaseThreeEastSouthExplorationSwitchingLaw



structure CaseOneExplorationSwitchingLaw where
  crossingA : P.V
  crossingB : P.V
  crossing_adj : P.G.Adj crossingA crossingB
  edges : Fin 4 -> M
  closed_not_mem : forall omega k,
    edges k ∉ D.exploration (setClosed s(crossingA, crossingB) omega)
  open_not_mem : forall omega k,
    edges k ∉ D.exploration (setOpen s(crossingA, crossingB) omega)

namespace CaseOneExplorationSwitchingLaw

variable (L : D.CaseOneExplorationSwitchingLaw)

def crossingEdge : Sym2 P.V := s(L.crossingA, L.crossingB)

def localSwitchingTable : D.LocalSwitchingTable where
  edges := L.edges
  toggle := localEdgeFlipEquiv L.crossingEdge
  pairedContribution := by
    intro omega
    refine ⟨0, ?_⟩
    intro k
    calc
      D.fermionicSummand omega (L.edges k) +
          D.fermionicSummand (localEdgeFlipEquiv L.crossingEdge omega) (L.edges k) =
        D.fermionicSummand (setClosed L.crossingEdge omega) (L.edges k) +
          D.fermionicSummand (setOpen L.crossingEdge omega) (L.edges k) :=
        pair_with_localEdgeFlip_eq_closed_add_open L.crossingEdge
          (fun rho => D.fermionicSummand rho (L.edges k)) omega
      _ = 0 := by
        unfold crossingEdge
        simp [fermionicSummand, L.closed_not_mem omega k,
          L.open_not_mem omega k]
      _ = isingF k 0 := by
        fin_cases k <;> simp [isingF]

theorem fermionicObservable_sHolo_relation :
    D.fermionicObservable (L.edges 0) + D.fermionicObservable (L.edges 1) =
      D.fermionicObservable (L.edges 2) + D.fermionicObservable (L.edges 3) :=
  (L.localSwitchingTable D).fermionicObservable_sHolo_relation D

end CaseOneExplorationSwitchingLaw




structure BalancedLocalSwitchingTable where
  edges : Fin 4 -> M
  toggle : ConfigSpace (Sym2 P.V) ≃ ConfigSpace (Sym2 P.V)
  pairedBalance : forall omega,
    (D.fermionicSummand omega (edges 0) +
        D.fermionicSummand (toggle omega) (edges 0)) -
      (D.fermionicSummand omega (edges 1) +
        D.fermionicSummand (toggle omega) (edges 1)) =
    Complex.I *
      ((D.fermionicSummand omega (edges 2) +
          D.fermionicSummand (toggle omega) (edges 2)) -
        (D.fermionicSummand omega (edges 3) +
          D.fermionicSummand (toggle omega) (edges 3)))

namespace BalancedLocalSwitchingTable

variable (T : D.BalancedLocalSwitchingTable)

private theorem sum_toggle (k : Fin 4) :
    (∑ omega : ConfigSpace (Sym2 P.V),
      D.fermionicSummand (T.toggle omega) (T.edges k)) =
      ∑ omega : ConfigSpace (Sym2 P.V),
        D.fermionicSummand omega (T.edges k) := by
  exact Equiv.sum_comp T.toggle
    (fun omega => D.fermionicSummand omega (T.edges k))

theorem fermionicObservable_contour_relation :
    D.fermionicObservable (T.edges 0) - D.fermionicObservable (T.edges 1) =
      Complex.I * (D.fermionicObservable (T.edges 2) -
        D.fermionicObservable (T.edges 3)) := by
  have hsum :
      (∑ omega : ConfigSpace (Sym2 P.V),
        ((D.fermionicSummand omega (T.edges 0) +
            D.fermionicSummand (T.toggle omega) (T.edges 0)) -
          (D.fermionicSummand omega (T.edges 1) +
            D.fermionicSummand (T.toggle omega) (T.edges 1)))) =
      ∑ omega : ConfigSpace (Sym2 P.V),
        Complex.I *
          ((D.fermionicSummand omega (T.edges 2) +
              D.fermionicSummand (T.toggle omega) (T.edges 2)) -
            (D.fermionicSummand omega (T.edges 3) +
              D.fermionicSummand (T.toggle omega) (T.edges 3))) := by
    apply Finset.sum_congr rfl
    intro omega _
    exact T.pairedBalance omega
  rw [← Finset.mul_sum] at hsum
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  rw [T.sum_toggle D 0, T.sum_toggle D 1,
    T.sum_toggle D 2, T.sum_toggle D 3] at hsum
  unfold fermionicObservable
  linear_combination (1 / 2 : Complex) * hsum

end BalancedLocalSwitchingTable



def balancedLocalSwitchingTableOfClosedOpen
    (crossingEdge : Sym2 P.V) (edges : Fin 4 -> M)
    (hbalance : D.ClosedOpenPairedBalance crossingEdge edges) :
    D.BalancedLocalSwitchingTable where
  edges := edges
  toggle := localEdgeFlipEquiv crossingEdge
  pairedBalance := by
    intro omega
    rw [pair_with_localEdgeFlip_eq_closed_add_open crossingEdge
        (fun rho => D.fermionicSummand rho (edges 0)) omega,
      pair_with_localEdgeFlip_eq_closed_add_open crossingEdge
        (fun rho => D.fermionicSummand rho (edges 1)) omega,
      pair_with_localEdgeFlip_eq_closed_add_open crossingEdge
        (fun rho => D.fermionicSummand rho (edges 2)) omega,
      pair_with_localEdgeFlip_eq_closed_add_open crossingEdge
        (fun rho => D.fermionicSummand rho (edges 3)) omega]
    exact hbalance omega

namespace CaseTwoExplorationSwitchingLaw

variable (L : D.CaseTwoExplorationSwitchingLaw)



def localSwitchingTable : D.BalancedLocalSwitchingTable :=
  balancedLocalSwitchingTableOfClosedOpen D L.crossingEdge L.edges
    L.paired_balance

theorem fermionicObservable_contour_relation :
    D.fermionicObservable (L.edges 0) - D.fermionicObservable (L.edges 1) =
      Complex.I * (D.fermionicObservable (L.edges 2) -
        D.fermionicObservable (L.edges 3)) :=
  (L.localSwitchingTable D).fermionicObservable_contour_relation D

end CaseTwoExplorationSwitchingLaw

namespace CaseThreeExplorationSwitchingLaw

variable (L : D.CaseThreeExplorationSwitchingLaw)

def localSwitchingTable : D.BalancedLocalSwitchingTable :=
  balancedLocalSwitchingTableOfClosedOpen D L.crossingEdge L.edges
    L.paired_balance

theorem fermionicObservable_contour_relation :
    D.fermionicObservable (L.edges 0) - D.fermionicObservable (L.edges 1) =
      Complex.I * (D.fermionicObservable (L.edges 2) -
        D.fermionicObservable (L.edges 3)) :=
  (L.localSwitchingTable D).fermionicObservable_contour_relation D

end CaseThreeExplorationSwitchingLaw

namespace CaseThreeEastSouthExplorationSwitchingLaw

variable (L : D.CaseThreeEastSouthExplorationSwitchingLaw)

def localSwitchingTable : D.BalancedLocalSwitchingTable :=
  balancedLocalSwitchingTableOfClosedOpen D L.crossingEdge L.edges
    L.paired_balance

theorem fermionicObservable_contour_relation :
    D.fermionicObservable (L.edges 0) - D.fermionicObservable (L.edges 1) =
      Complex.I * (D.fermionicObservable (L.edges 2) -
        D.fermionicObservable (L.edges 3)) :=
  (L.localSwitchingTable D).fermionicObservable_contour_relation D

end CaseThreeEastSouthExplorationSwitchingLaw




inductive PointwiseExplorationSwitchingCase
    (crossingEdge : Sym2 P.V) (edges : Fin 4 -> M)
    (omega : ConfigSpace (Sym2 P.V)) : Type
  | caseOne
      (closed_not_mem : forall k,
        edges k ∉ D.exploration (setClosed crossingEdge omega))
      (open_not_mem : forall k,
        edges k ∉ D.exploration (setOpen crossingEdge omega))
  | caseTwo
      (paired_balance :
        (D.fermionicSummand (setClosed crossingEdge omega) (edges 0) +
            D.fermionicSummand (setOpen crossingEdge omega) (edges 0)) -
          (D.fermionicSummand (setClosed crossingEdge omega) (edges 1) +
            D.fermionicSummand (setOpen crossingEdge omega) (edges 1)) =
        Complex.I *
          ((D.fermionicSummand (setClosed crossingEdge omega) (edges 2) +
              D.fermionicSummand (setOpen crossingEdge omega) (edges 2)) -
            (D.fermionicSummand (setClosed crossingEdge omega) (edges 3) +
              D.fermionicSummand (setOpen crossingEdge omega) (edges 3))))
  | caseThree
      (paired_balance :
        (D.fermionicSummand (setClosed crossingEdge omega) (edges 0) +
            D.fermionicSummand (setOpen crossingEdge omega) (edges 0)) -
          (D.fermionicSummand (setClosed crossingEdge omega) (edges 1) +
            D.fermionicSummand (setOpen crossingEdge omega) (edges 1)) =
        Complex.I *
          ((D.fermionicSummand (setClosed crossingEdge omega) (edges 2) +
              D.fermionicSummand (setOpen crossingEdge omega) (edges 2)) -
            (D.fermionicSummand (setClosed crossingEdge omega) (edges 3) +
              D.fermionicSummand (setOpen crossingEdge omega) (edges 3))))

namespace CaseTwoExplorationSwitchingLaw



def pointwiseCase (L : D.CaseTwoExplorationSwitchingLaw)
    (omega : ConfigSpace (Sym2 P.V)) :
    D.PointwiseExplorationSwitchingCase L.crossingEdge L.edges omega :=
  .caseTwo (L.paired_balance omega)

end CaseTwoExplorationSwitchingLaw

namespace CaseThreeExplorationSwitchingLaw


def pointwiseCase (L : D.CaseThreeExplorationSwitchingLaw)
    (omega : ConfigSpace (Sym2 P.V)) :
    D.PointwiseExplorationSwitchingCase L.crossingEdge L.edges omega :=
  .caseThree (L.paired_balance omega)

end CaseThreeExplorationSwitchingLaw

namespace CaseThreeEastSouthExplorationSwitchingLaw



def pointwiseCase (L : D.CaseThreeEastSouthExplorationSwitchingLaw)
    (omega : ConfigSpace (Sym2 P.V)) :
    D.PointwiseExplorationSwitchingCase L.crossingEdge L.edges omega :=
  .caseThree (L.paired_balance omega)

end CaseThreeEastSouthExplorationSwitchingLaw

namespace CaseOneExplorationSwitchingLaw


def pointwiseCase (L : D.CaseOneExplorationSwitchingLaw)
    (omega : ConfigSpace (Sym2 P.V)) :
    D.PointwiseExplorationSwitchingCase L.crossingEdge L.edges omega :=
  .caseOne (L.closed_not_mem omega) (L.open_not_mem omega)

end CaseOneExplorationSwitchingLaw



structure ExhaustiveExplorationSwitchingLaw where
  crossingEdge : Sym2 P.V
  edges : Fin 4 -> M
  caseAt : forall omega,
    D.PointwiseExplorationSwitchingCase crossingEdge edges omega

namespace ExhaustiveExplorationSwitchingLaw

variable (L : D.ExhaustiveExplorationSwitchingLaw)



def localSwitchingTable : D.BalancedLocalSwitchingTable where
  edges := L.edges
  toggle := localEdgeFlipEquiv L.crossingEdge
  pairedBalance := by
    intro omega
    have hpair (k : Fin 4) :
        D.fermionicSummand omega (L.edges k) +
            D.fermionicSummand
              (localEdgeFlipEquiv L.crossingEdge omega) (L.edges k) =
          D.fermionicSummand (setClosed L.crossingEdge omega) (L.edges k) +
            D.fermionicSummand (setOpen L.crossingEdge omega) (L.edges k) :=
      pair_with_localEdgeFlip_eq_closed_add_open L.crossingEdge
        (fun rho => D.fermionicSummand rho (L.edges k)) omega
    cases hcase : L.caseAt omega with
    | caseOne hclosed hopen =>
        rw [hpair 0, hpair 1, hpair 2, hpair 3]
        simp [fermionicSummand, hclosed, hopen]
    | caseTwo hbalanced =>
        rw [hpair 0, hpair 1, hpair 2, hpair 3]
        exact hbalanced
    | caseThree hbalanced =>
        rw [hpair 0, hpair 1, hpair 2, hpair 3]
        exact hbalanced

theorem fermionicObservable_contour_relation :
    D.fermionicObservable (L.edges 0) - D.fermionicObservable (L.edges 1) =
      Complex.I * (D.fermionicObservable (L.edges 2) -
        D.fermionicObservable (L.edges 3)) :=
  (L.localSwitchingTable D).fermionicObservable_contour_relation D

end ExhaustiveExplorationSwitchingLaw

end FKIsingDobrushinDomain

end

end StatMech.Universality
