/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.AnisotropicSquareTorusKacWard
import Code.FrontierA.QuantumIsingTrotterCylinder
import Code.Onsager.TorusIntersection










open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager



def squareTorusPositiveDirection (mu : Fin 2) : Fin 4 :=
  ⟨mu.val, lt_trans mu.isLt (by omega)⟩

@[simp] theorem squareTorusPositiveDirection_zero :
    squareTorusPositiveDirection 0 = 0 := rfl

@[simp] theorem squareTorusPositiveDirection_one :
    squareTorusPositiveDirection 1 = 1 := rfl

def squareTorusPositiveEdgeMap (L : Nat) [Fact (2 < L)] :
    ((ZMod L × ZMod L) × Fin 2) →
      {edge // edge ∈ (onsTorusGraph L).edgeFinset} :=
  fun p ↦ ⟨ons_portEdge L (p.1, squareTorusPositiveDirection p.2),
    ons_portEdge_mem_edgeFinset L _⟩

theorem squareTorusPositiveEdgeMap_injective
    (L : Nat) [Fact (2 < L)] :
    Function.Injective (squareTorusPositiveEdgeMap L) := by
  rintro ⟨p, mu⟩ ⟨q, nu⟩ h
  have hedge : ons_portEdge L (q, squareTorusPositiveDirection nu) =
      ons_portEdge L (p, squareTorusPositiveDirection mu) :=
    (congrArg Subtype.val h).symm
  rcases (ons_portEdge_eq_iff L
      (p, squareTorusPositiveDirection mu)
      (q, squareTorusPositiveDirection nu)).mp hedge with hsame | hreverse
  · apply Prod.ext
    · exact (congrArg Prod.fst hsame).symm
    · apply Fin.ext
      exact (congrArg (fun d ↦ d.2.val) hsame).symm
  · exfalso
    have hdir := congrArg (fun d ↦ d.2) hreverse
    fin_cases mu <;> fin_cases nu <;> simp [ons_dartRev] at hdir

theorem squareTorusPositiveEdgeMap_surjective
    (L : Nat) [Fact (2 < L)] :
    Function.Surjective (squareTorusPositiveEdgeMap L) := by
  intro edge
  obtain ⟨⟨p, mu⟩, hp⟩ := ons_torusEdge_eq_portEdge L edge.property
  fin_cases mu
  · refine ⟨(p, 0), ?_⟩
    apply Subtype.ext
    exact hp
  · refine ⟨(p, 1), ?_⟩
    apply Subtype.ext
    exact hp
  · refine ⟨((p.1 - 1, p.2), 0), ?_⟩
    apply Subtype.ext
    exact (ons_portEdge_west_eq_horizontal L p).symm.trans hp
  · refine ⟨((p.1, p.2 - 1), 1), ?_⟩
    apply Subtype.ext
    exact (ons_portEdge_south_eq_vertical L p).symm.trans hp



noncomputable def squareTorusPositiveEdgeEquiv
    (L : Nat) [Fact (2 < L)] :
    ((ZMod L × ZMod L) × Fin 2) ≃
      {edge // edge ∈ (onsTorusGraph L).edgeFinset} :=
  Equiv.ofBijective (squareTorusPositiveEdgeMap L)
    ⟨squareTorusPositiveEdgeMap_injective L,
      squareTorusPositiveEdgeMap_surjective L⟩



theorem sum_squareTorus_edges_eq_positive_directions
    (L : Nat) [Fact (2 < L)]
    (f : Sym2 (ZMod L × ZMod L) → Real) :
    (∑ edge ∈ (onsTorusGraph L).edgeFinset, f edge) =
      ∑ p : ZMod L × ZMod L,
        (f (ons_portEdge L (p, 0)) + f (ons_portEdge L (p, 1))) := by
  have hsum := Equiv.sum_comp (squareTorusPositiveEdgeEquiv L)
    (fun edge : {edge // edge ∈ (onsTorusGraph L).edgeFinset} ↦ f edge.1)
  rw [Finset.sum_subtype (onsTorusGraph L).edgeFinset]
  · rw [← hsum]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro p _
    rw [Fin.sum_univ_two]
    rfl
  · intro edge
    rw [SimpleGraph.mem_edgeFinset]


theorem prod_squareTorus_edges_eq_positive_directions
    (L : Nat) [Fact (2 < L)]
    (f : Sym2 (ZMod L × ZMod L) → Real) :
    (∏ edge ∈ (onsTorusGraph L).edgeFinset, f edge) =
      ∏ p : ZMod L × ZMod L,
        (f (ons_portEdge L (p, 0)) * f (ons_portEdge L (p, 1))) := by
  have hprod := Equiv.prod_comp (squareTorusPositiveEdgeEquiv L)
    (fun edge : {edge // edge ∈ (onsTorusGraph L).edgeFinset} ↦ f edge.1)
  rw [Finset.prod_subtype (onsTorusGraph L).edgeFinset]
  · rw [← hprod]
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro p _
    rw [Fin.prod_univ_two]
    rfl
  · intro edge
    rw [SimpleGraph.mem_edgeFinset]




noncomputable def quantumIsingSquareConfigEquiv
    (L : Nat) [NeZero L] :
    (Fin L → QuantumIsingChainConfig L) ≃
      ConfigSpace (ZMod L × ZMod L) where
  toFun omega p :=
    omega ((ZMod.finEquiv L).symm p.2) ((ZMod.finEquiv L).symm p.1)
  invFun sigma k i := sigma (ZMod.finEquiv L i, ZMod.finEquiv L k)
  left_inv omega := by
    funext k i
    simp
  right_inv sigma := by
    funext p
    simp

@[simp] theorem quantumIsingSquareConfigEquiv_apply
    (L : Nat) [NeZero L]
    (omega : Fin L → QuantumIsingChainConfig L) (k i : Fin L) :
    quantumIsingSquareConfigEquiv L omega
        (ZMod.finEquiv L i, ZMod.finEquiv L k) = omega k i := by
  simp [quantumIsingSquareConfigEquiv]

theorem finEquiv_quantumIsingCyclicSucc
    (L : Nat) [NeZero L] (i : Fin L) :
    ZMod.finEquiv L (quantumIsingCyclicSucc i) =
      ZMod.finEquiv L i + 1 := by
  rw [quantumIsingCyclicSucc_eq_add_one]
  simpa using (ZMod.finEquiv L).map_add i 1



noncomputable def quantumIsingSquareTorusCoupling
    (beta h : Real) (L : Nat) :
    Sym2 (ZMod L × ZMod L) → Real :=
  fun edge ↦ if squareTorusHorizontalEdge L edge then
    beta / (4 * L)
  else quantumIsingVerticalCoupling beta h L

@[simp] theorem quantumIsingSquareTorusCoupling_horizontal
    (beta h : Real) (L : Nat) [Fact (2 < L)]
    (p : ZMod L × ZMod L) :
    quantumIsingSquareTorusCoupling beta h L (ons_portEdge L (p, 0)) =
      beta / (4 * L) := by
  rw [quantumIsingSquareTorusCoupling, if_pos]
  exact ⟨p, rfl⟩

@[simp] theorem quantumIsingSquareTorusCoupling_vertical
    (beta h : Real) (L : Nat) [Fact (2 < L)]
    (p : ZMod L × ZMod L) :
    quantumIsingSquareTorusCoupling beta h L (ons_portEdge L (p, 1)) =
      quantumIsingVerticalCoupling beta h L := by
  rw [quantumIsingSquareTorusCoupling, if_neg]
  rintro ⟨q, hq⟩
  have heq := (ons_portEdge_eq_iff L (p, 1) (q, 0)).mp hq.symm
  rcases heq with heq | heq
  · have hdir := congrArg Prod.snd heq
    norm_num at hdir
  · have hdir := congrArg Prod.snd heq
    simp [ons_dartRev] at hdir

theorem sum_zmod_square_eq_fin_square
    (L : Nat) [NeZero L]
    (f : ZMod L × ZMod L → Real) :
    (∑ p : ZMod L × ZMod L, f p) =
      ∑ k : Fin L, ∑ i : Fin L,
        f (ZMod.finEquiv L i, ZMod.finEquiv L k) := by
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : ZMod L, ∑ y : ZMod L, f (x, y)) =
        ∑ i : Fin L, ∑ y : ZMod L,
          f (ZMod.finEquiv L i, y) :=
      (Equiv.sum_comp (ZMod.finEquiv L).toEquiv
        (fun x : ZMod L ↦ ∑ y : ZMod L, f (x, y))).symm
    _ = ∑ i : Fin L, ∑ k : Fin L,
          f (ZMod.finEquiv L i, ZMod.finEquiv L k) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Equiv.sum_comp (ZMod.finEquiv L).toEquiv
        (fun y : ZMod L ↦ f (ZMod.finEquiv L i, y))).symm
    _ = _ := Finset.sum_comm



noncomputable def quantumIsingSquareTrotterEnergy
    (beta h : Real) (L : Nat)
    (omega : Fin L → QuantumIsingChainConfig L) : Real :=
  (∑ k : Fin L,
      beta / (4 * L) * quantumIsingChainInteraction L (omega k)) +
    ∑ k : Fin L, ∑ i : Fin L,
      quantumIsingVerticalCoupling beta h L *
        (quantumIsingSpinSign (omega k i) *
          quantumIsingSpinSign
            (omega (quantumIsingCyclicSucc k) i))



theorem quantumIsingSquareTorus_energy_eq
    (beta h : Real) (L : Nat) [Fact (2 < L)]
    (omega : Fin L → QuantumIsingChainConfig L) :
    (∑ edge ∈ (onsTorusGraph L).edgeFinset,
      quantumIsingSquareTorusCoupling beta h L edge *
        bond (quantumIsingSquareConfigEquiv L omega) edge) =
      quantumIsingSquareTrotterEnergy beta h L omega := by
  rw [sum_squareTorus_edges_eq_positive_directions]
  rw [sum_zmod_square_eq_fin_square]
  simp only [quantumIsingSquareTorusCoupling_horizontal,
    quantumIsingSquareTorusCoupling_vertical]
  simp only [ons_portEdge, ons_dirStep, bond_mk]
  simp_rw [← finEquiv_quantumIsingCyclicSucc]
  unfold spin
  simp only [quantumIsingSquareConfigEquiv_apply]
  unfold quantumIsingSquareTrotterEnergy quantumIsingChainInteraction
    quantumIsingSpinSign
  calc
    (∑ k : Fin L, ∑ i : Fin L,
        (beta / (4 * (L : Real)) *
            ((if omega k i = true then 1 else -1) *
              if omega k (quantumIsingCyclicSucc i) = true then 1 else -1) +
          quantumIsingVerticalCoupling beta h L *
            ((if omega k i = true then 1 else -1) *
              if omega (quantumIsingCyclicSucc k) i = true then 1 else -1))) =
        (∑ k : Fin L, ∑ i : Fin L,
          beta / (4 * (L : Real)) *
            ((if omega k i = true then 1 else -1) *
              if omega k (quantumIsingCyclicSucc i) = true then 1 else -1)) +
        ∑ k : Fin L, ∑ i : Fin L,
          quantumIsingVerticalCoupling beta h L *
            ((if omega k i = true then 1 else -1) *
              if omega (quantumIsingCyclicSucc k) i = true then 1 else -1) := by
      simp only [Finset.sum_add_distrib]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]



theorem quantumIsingClassicalCylinderWeight_diagonal_eq_exp_energy
    (beta h : Real) (L : Nat)
    (omega : Fin L → QuantumIsingChainConfig L) :
    quantumIsingClassicalCylinderWeight beta h L L omega =
      Real.exp (quantumIsingSquareTrotterEnergy beta h L omega) := by
  unfold quantumIsingClassicalCylinderWeight
    quantumIsingSpatialTrotterWeight quantumIsingVerticalBondWeight
  simp_rw [← Real.exp_sum, ← Real.exp_add]
  rw [← Real.exp_sum]
  apply congrArg Real.exp
  unfold quantumIsingSquareTrotterEnergy
  rw [Finset.sum_add_distrib]



theorem quantumIsingClassicalCylinderWeight_eq_torus_wJ
    (beta h : Real) (L : Nat) [Fact (2 < L)]
    (omega : Fin L → QuantumIsingChainConfig L) :
    quantumIsingClassicalCylinderWeight beta h L L omega =
      StatMech.Sharpness.wJ (onsTorusGraph L).edgeFinset
        (quantumIsingSquareTorusCoupling beta h L) (fun _ ↦ 0)
        (quantumIsingSquareConfigEquiv L omega) := by
  rw [quantumIsingClassicalCylinderWeight_diagonal_eq_exp_energy]
  unfold StatMech.Sharpness.wJ
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  rw [quantumIsingSquareTorus_energy_eq]



theorem quantumIsingClassicalCylinderPartition_eq_torus_ZJ
    (beta h : Real) (L : Nat) [Fact (2 < L)] :
    quantumIsingClassicalCylinderPartition beta h L L =
      StatMech.Sharpness.ZJ (onsTorusGraph L).edgeFinset
        (quantumIsingSquareTorusCoupling beta h L) (fun _ ↦ 0) := by
  unfold quantumIsingClassicalCylinderPartition StatMech.Sharpness.ZJ
  rw [← Equiv.sum_comp (quantumIsingSquareConfigEquiv L)
    (StatMech.Sharpness.wJ (onsTorusGraph L).edgeFinset
      (quantumIsingSquareTorusCoupling beta h L) (fun _ ↦ 0))]
  apply Finset.sum_congr rfl
  intro omega _
  exact quantumIsingClassicalCylinderWeight_eq_torus_wJ beta h L omega

noncomputable def quantumIsingSquareTorusTanhWeight
    (beta h : Real) (L : Nat) :
    Sym2 (ZMod L × ZMod L) → Real :=
  fun edge ↦ if squareTorusHorizontalEdge L edge then
    Real.tanh (beta / (4 * L))
  else Real.tanh (quantumIsingVerticalCoupling beta h L)

theorem tanh_quantumIsingSquareTorusCoupling
    (beta h : Real) (L : Nat) :
    (fun edge ↦ Real.tanh (quantumIsingSquareTorusCoupling beta h L edge)) =
      quantumIsingSquareTorusTanhWeight beta h L := by
  funext edge
  unfold quantumIsingSquareTorusCoupling quantumIsingSquareTorusTanhWeight
  split <;> rfl

theorem coe_quantumIsingSquareTorusTanhWeight
    (beta h : Real) (L : Nat) :
    (fun edge ↦ (quantumIsingSquareTorusTanhWeight beta h L edge : Complex)) =
      anisotropicSquareEdgeWeight L
        (Real.tanh (beta / (4 * L)))
        (Real.tanh (quantumIsingVerticalCoupling beta h L)) := by
  funext edge
  unfold quantumIsingSquareTorusTanhWeight anisotropicSquareEdgeWeight
  split <;> rfl

theorem prod_cosh_quantumIsingSquareTorusCoupling
    (beta h : Real) (L : Nat) [Fact (2 < L)] :
    (∏ edge ∈ (onsTorusGraph L).edgeFinset,
        Real.cosh (quantumIsingSquareTorusCoupling beta h L edge)) =
      (Real.cosh (beta / (4 * L)) *
        Real.cosh (quantumIsingVerticalCoupling beta h L)) ^ (L * L) := by
  rw [prod_squareTorus_edges_eq_positive_directions]
  simp only [quantumIsingSquareTorusCoupling_horizontal,
    quantumIsingSquareTorusCoupling_vertical, Finset.prod_const,
    Finset.card_univ, Fintype.card_prod, ZMod.card]



theorem quantumIsingClassicalCylinderPartition_highTemperature
    (beta h : Real) (L : Nat) [Fact (2 < L)] :
    quantumIsingClassicalCylinderPartition beta h L L =
      (2 : Real) ^ (L * L) *
        (Real.cosh (beta / (4 * L)) *
          Real.cosh (quantumIsingVerticalCoupling beta h L)) ^ (L * L) *
        inhomogeneousEvenSubgraphSum (onsTorusGraph L)
          (quantumIsingSquareTorusTanhWeight beta h L) := by
  rw [quantumIsingClassicalCylinderPartition_eq_torus_ZJ,
    inhomogeneousIsingPartition_highTemperature,
    prod_cosh_quantumIsingSquareTorusCoupling,
    tanh_quantumIsingSquareTorusCoupling]
  congr 3
  simp only [Fintype.card_prod, ZMod.card]



theorem two_mul_quantumIsingClassicalCylinderPartition_eq_spin
    (beta h : Real) (L : Nat) [Fact (2 < L)] :
    (2 : Complex) *
        quantumIsingClassicalCylinderPartition beta h L L =
      ((2 : Real) ^ (L * L) *
          (Real.cosh (beta / (4 * L)) *
            Real.cosh (quantumIsingVerticalCoupling beta h L)) ^ (L * L) :
        Real) *
        (ons_weightedSpinCharacterSum L
            (anisotropicSquareEdgeWeight L
              (Real.tanh (beta / (4 * L)))
              (Real.tanh (quantumIsingVerticalCoupling beta h L))) 1 1 +
          ons_weightedSpinCharacterSum L
            (anisotropicSquareEdgeWeight L
              (Real.tanh (beta / (4 * L)))
              (Real.tanh (quantumIsingVerticalCoupling beta h L))) 0 1 +
          ons_weightedSpinCharacterSum L
            (anisotropicSquareEdgeWeight L
              (Real.tanh (beta / (4 * L)))
              (Real.tanh (quantumIsingVerticalCoupling beta h L))) 1 0 -
          ons_weightedSpinCharacterSum L
            (anisotropicSquareEdgeWeight L
              (Real.tanh (beta / (4 * L)))
              (Real.tanh (quantumIsingVerticalCoupling beta h L))) 0 0) := by
  let prefactor : Real :=
    (2 : Real) ^ (L * L) *
      (Real.cosh (beta / (4 * L)) *
        Real.cosh (quantumIsingVerticalCoupling beta h L)) ^ (L * L)
  let evenSum : Real := inhomogeneousEvenSubgraphSum (onsTorusGraph L)
    (quantumIsingSquareTorusTanhWeight beta h L)
  have hpartition :
      quantumIsingClassicalCylinderPartition beta h L L =
        prefactor * evenSum := by
    exact quantumIsingClassicalCylinderPartition_highTemperature beta h L
  have harf := two_mul_inhomogeneousEvenSubgraphSum_eq_spin L
    (quantumIsingSquareTorusTanhWeight beta h L)
  rw [coe_quantumIsingSquareTorusTanhWeight] at harf
  rw [hpartition]
  calc
    (2 : Complex) * ((prefactor * evenSum : Real) : Complex) =
        (prefactor : Complex) * ((2 : Complex) * (evenSum : Complex)) := by
      push_cast
      ring
    _ = (prefactor : Complex) * _ := by rw [harf]

end StatMech.FrontierA
