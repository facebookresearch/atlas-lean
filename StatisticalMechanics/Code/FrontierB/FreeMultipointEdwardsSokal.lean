/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FK.EsCorrelations
import Code.IsingFK.Q2
import Code.Ising.GKS

open scoped BigOperators

namespace StatMech.FK

open StatMech.ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def clusterMarkCount (omega : ConfigSpace (Sym2 V)) (A : Finset V)
    (C : (openSub G omega).ConnectedComponent) : Nat := by
  classical
  exact (A.filter fun x => (openSub G omega).connectedComponentMk x = C).card



def AllClustersEven (omega : ConfigSpace (Sym2 V)) (A : Finset V) : Prop :=
  ∀ C : (openSub G omega).ConnectedComponent, Even (clusterMarkCount G omega A C)

noncomputable instance instDecidableEqOpenConnectedComponent
    (omega : ConfigSpace (Sym2 V)) :
    DecidableEq (openSub G omega).ConnectedComponent :=
  Classical.decEq _

noncomputable instance instDecidableAllClustersEven (omega : ConfigSpace (Sym2 V))
    (A : Finset V) : Decidable (AllClustersEven G omega A) :=
  Classical.propDecidable _


def esSpinProduct (A : Finset V) (sigma : V -> Fin 2) : Real :=
  ∏ x ∈ A, isingSpin (sigma x)

theorem esSpinProduct_constOnOpenEquiv (omega : ConfigSpace (Sym2 V))
    (A : Finset V) (tau : (openSub G omega).ConnectedComponent -> Fin 2) :
    esSpinProduct A ((constOnOpenEquiv G omega tau).1) =
      ∏ C : (openSub G omega).ConnectedComponent,
        isingSpin (tau C) ^ clusterMarkCount G omega A C := by
  classical
  unfold esSpinProduct clusterMarkCount
  change (∏ x ∈ A,
      isingSpin (tau ((openSub G omega).connectedComponentMk x))) = _
  rw [← Finset.prod_fiberwise' A
    (fun x => (openSub G omega).connectedComponentMk x)
    (fun C => isingSpin (tau C))]
  apply Fintype.prod_congr
  intro C
  rw [Finset.prod_const]

theorem sum_isingSpin_pow (n : Nat) :
    (∑ a : Fin 2, isingSpin a ^ n) = if Even n then 2 else 0 := by
  by_cases h : Even n
  · rw [Fin.sum_univ_two]
    simp [isingSpin, h, h.neg_one_pow]
    norm_num
  · rw [Fin.sum_univ_two]
    simp [isingSpin, h, neg_one_pow_eq_ite]




theorem clusterColor_spinProduct_sum (omega : ConfigSpace (Sym2 V))
    (A : Finset V) :
    (∑ tau : (openSub G omega).ConnectedComponent -> Fin 2,
        esSpinProduct A ((constOnOpenEquiv G omega tau).1)) =
      if AllClustersEven G omega A then 2 ^ numClusters G omega else 0 := by
  classical
  simp_rw [esSpinProduct_constOnOpenEquiv G omega A]
  calc
    (∑ tau : (openSub G omega).ConnectedComponent -> Fin 2,
        ∏ C, isingSpin (tau C) ^ clusterMarkCount G omega A C) =
        ∏ C : (openSub G omega).ConnectedComponent,
          ∑ a : Fin 2, isingSpin a ^ clusterMarkCount G omega A C := by
            simpa [Fintype.piFinset_univ] using
              (Finset.sum_prod_piFinset (Finset.univ : Finset (Fin 2))
                (fun C a => isingSpin a ^ clusterMarkCount G omega A C))
    _ = ∏ C : (openSub G omega).ConnectedComponent,
          if Even (clusterMarkCount G omega A C) then 2 else 0 := by
            apply Fintype.prod_congr
            intro C
            exact sum_isingSpin_pow (clusterMarkCount G omega A C)
    _ = if AllClustersEven G omega A then 2 ^ numClusters G omega else 0 := by
          by_cases hEven : AllClustersEven G omega A
          · rw [if_pos hEven]
            simp_rw [if_pos (hEven _)]
            simp [numClusters]
          · rw [if_neg hEven]
            have hnot : ¬ ∀ C : (openSub G omega).ConnectedComponent,
                Even (clusterMarkCount G omega A C) := by
              simpa [AllClustersEven] using hEven
            rw [Classical.not_forall] at hnot
            obtain ⟨C, hC⟩ := hnot
            apply Finset.prod_eq_zero (Finset.mem_univ C)
            rw [if_neg hC]



theorem compatible_esSpinProduct_sum (omega : ConfigSpace (Sym2 V))
    (A : Finset V) :
    (∑ sigma : V -> Fin 2,
        (if ConstOnOpen G omega sigma then (1 : Real) else 0) *
          esSpinProduct A sigma) =
      if AllClustersEven G omega A then 2 ^ numClusters G omega else 0 := by
  classical
  calc
    (∑ sigma : V -> Fin 2,
        (if ConstOnOpen G omega sigma then (1 : Real) else 0) *
          esSpinProduct A sigma) =
        ∑ sigma ∈ Finset.univ.filter (ConstOnOpen G omega),
          esSpinProduct A sigma := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro sigma hsigma
            by_cases h : ConstOnOpen G omega sigma
            · simp [h]
            · simp [h]
    _ = ∑ sigma : {sigma : V -> Fin 2 // ConstOnOpen G omega sigma},
          esSpinProduct A sigma.1 := by
            rw [Finset.sum_subtype]
            intro sigma
            simp
    _ = ∑ tau : (openSub G omega).ConnectedComponent -> Fin 2,
          esSpinProduct A ((constOnOpenEquiv G omega tau).1) := by
            symm
            exact (constOnOpenEquiv G omega).sum_comp
              (fun sigma => esSpinProduct A sigma.1)
    _ = if AllClustersEven G omega A then 2 ^ numClusters G omega else 0 :=
      clusterColor_spinProduct_sum G omega A



theorem esWeight_multipoint_spin_sum (p : Real)
    (omega : ConfigSpace (Sym2 V)) (A : Finset V) :
    (∑ sigma : V -> Fin 2,
        esWeight G p sigma omega * esSpinProduct A sigma) =
      if AllClustersEven G omega A then fkWeight G p (2 : Real) omega else 0 := by
  rw [esWeight_spinsum_factor,
    compatible_esSpinProduct_sum G omega A]
  by_cases hEven : AllClustersEven G omega A
  · rw [if_pos hEven, if_pos hEven]
    rfl
  · rw [if_neg hEven, if_neg hEven, mul_zero]


noncomputable def esMultiPoint (p : Real) (A : Finset V) : Real :=
  (∑ omega : ConfigSpace (Sym2 V), ∑ sigma : V -> Fin 2,
      esWeight G p sigma omega * esSpinProduct A sigma) / esZ G 2 p



noncomputable def allClustersEvenProb (p : Real) (A : Finset V) : Real :=
  ∑ omega ∈ Finset.univ.filter (fun omega : ConfigSpace (Sym2 V) =>
      AllClustersEven G omega A), fkProb G p 2 omega


theorem esMultiPoint_eq_allClustersEvenProb (p : Real) (A : Finset V) :
    esMultiPoint G p A = allClustersEvenProb G p A := by
  classical
  unfold esMultiPoint allClustersEvenProb fkProb
  rw [Finset.sum_congr rfl
    (fun omega _ => esWeight_multipoint_spin_sum G p omega A)]
  rw [esZ_eq_fkZ, Nat.cast_ofNat, Finset.sum_div]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun omega : ConfigSpace (Sym2 V) => AllClustersEven G omega A)]
  have hzero :
      (∑ omega ∈ Finset.univ.filter (fun omega : ConfigSpace (Sym2 V) =>
          ¬ AllClustersEven G omega A),
        (if AllClustersEven G omega A then fkWeight G p (2 : Real) omega else 0) /
          fkZ G p 2) = 0 := by
    apply Finset.sum_eq_zero
    intro omega homega
    rw [if_neg (Finset.mem_filter.mp homega).2, zero_div]
  rw [hzero, add_zero]
  apply Finset.sum_congr rfl
  intro omega homega
  rw [if_pos (Finset.mem_filter.mp homega).2]

omit [Fintype V] [DecidableEq V] in
theorem isingSpin_eq_neg_spin_toIsing (sigma : V -> Fin 2) (x : V) :
    isingSpin (sigma x) = -Ising.spin (IsingFK.toIsing sigma) x := by
  generalize ha : sigma x = a
  fin_cases a <;>
    simp only [isingSpin, Ising.spin, IsingFK.toIsing, ha,
      finTwoEquiv, Equiv.coe_fn_mk]
    <;> norm_num

omit [Fintype V] [DecidableEq V] in
theorem esSpinProduct_eq_negOnePow_mul_spinProd_toIsing (A : Finset V)
    (sigma : V -> Fin 2) :
    esSpinProduct A sigma = (-1 : Real) ^ A.card *
      Ising.spinProd A (IsingFK.toIsing sigma) := by
  unfold esSpinProduct Ising.spinProd
  simp_rw [isingSpin_eq_neg_spin_toIsing]
  calc
    (∏ x ∈ A, -Ising.spin (IsingFK.toIsing sigma) x) =
        ∏ x ∈ A, (-1 : Real) * Ising.spin (IsingFK.toIsing sigma) x := by
          apply Finset.prod_congr rfl
          intro x hx
          ring
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]

omit [Fintype V] [DecidableEq V] in
theorem esSpinProduct_eq_spinProd_toIsing_of_even (A : Finset V)
    (hA : Even A.card) (sigma : V -> Fin 2) :
    esSpinProduct A sigma = Ising.spinProd A (IsingFK.toIsing sigma) := by
  rw [esSpinProduct_eq_negOnePow_mul_spinProd_toIsing, hA.neg_one_pow, one_mul]

theorem esMultiPoint_eq_firstMarginal_sum (p : Real) (A : Finset V) :
    esMultiPoint G p A =
      ∑ sigma : V -> Fin 2,
        esFirstMarginal G 2 p sigma * esSpinProduct A sigma := by
  unfold esMultiPoint esFirstMarginal
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro sigma hsigma
  rw [← Finset.sum_mul]
  ring




theorem isingExpectation_spinProd_eq_allClustersEvenProb
    (beta : Real) (A : Finset V) (hA : Even A.card) :
    Ising.isingExpectation G beta 0 (Ising.spinProd A) =
      allClustersEvenProb G (1 - Real.exp (-2 * beta)) A := by
  let e : (V -> Fin 2) ≃ ConfigSpace V :=
    Equiv.ofBijective _ IsingFK.toIsing_bijective
  calc
    Ising.isingExpectation G beta 0 (Ising.spinProd A) =
        ∑ sigma : V -> Fin 2,
          Ising.isingProb G beta 0 (IsingFK.toIsing sigma) *
            Ising.spinProd A (IsingFK.toIsing sigma) := by
              unfold Ising.isingExpectation
              simpa [e, Equiv.ofBijective_apply] using
                (e.sum_comp (fun s =>
                  Ising.isingProb G beta 0 s * Ising.spinProd A s)).symm
    _ = ∑ sigma : V -> Fin 2,
          esFirstMarginal G 2 (1 - Real.exp (-2 * beta)) sigma *
            esSpinProduct A sigma := by
              apply Finset.sum_congr rfl
              intro sigma hsigma
              rw [IsingFK.isingProb_eq_pottsProb G beta (2 * beta) 1 (by ring),
                ← esFirstMarginal_eq_pottsProb G 2 (2 * beta) 1]
              simp only [mul_one]
              ring_nf
              rw [esSpinProduct_eq_spinProd_toIsing_of_even A hA]
    _ = esMultiPoint G (1 - Real.exp (-2 * beta)) A :=
      (esMultiPoint_eq_firstMarginal_sum G _ A).symm
    _ = allClustersEvenProb G (1 - Real.exp (-2 * beta)) A :=
      esMultiPoint_eq_allClustersEvenProb G _ A

end StatMech.FK
