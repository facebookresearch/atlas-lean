/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalRadialPatch










namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section



def fkIsingSquareRadialPatchPrimalGraph
    (n m : Nat) (hm : m ≤ n) :
    SimpleGraph (FKIsingSquareRadialPatchPrimalNode m) :=
  SimpleGraph.comap (fkIsingSquareRadialPatchPrimalNodeVertex n m hm)
    (fkSquareBoxPlanar n).G


def fkIsingSquareRadialPatchPrimalBoundary
    (m : Nat) (p : FKIsingSquareRadialPatchPrimalNode m) : Prop :=
  p.1.1.1 = 0 ∨ p.1.1.1 + 1 = m ∨
    p.1.2.1 = 0 ∨ p.1.2.1 + 1 = m


def fkIsingSquareRadialPatchPrimalValue
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (p : FKIsingSquareRadialPatchPrimalNode m) : Real :=
  base + fkIsingSquareRadialPatchPrimitive
    n m hn hm hmpos p.1.1.1 p.1.2.1



theorem fkIsingSquareRadialPatchPrimalGraph_laplacian_eq_diagonal
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (heven : Even (i + j)) :
    isingFiniteGraphLaplacian (fkIsingSquareRadialPatchPrimalGraph n m hm)
        (fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base)
        ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), heven⟩ =
      fkIsingSquareRadialPatchDiagonalLaplacian
        (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos) i j := by
  classical
  let c : FKIsingSquareRadialPatchPrimalNode m :=
    ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), heven⟩
  let ne : FKIsingSquareRadialPatchPrimalNode m :=
    ⟨(⟨i + 1, hi1⟩, ⟨j + 1, hj1⟩), by
      change Even ((i + 1) + (j + 1))
      rw [Nat.even_iff]
      have hmod := Nat.even_iff.mp heven
      omega⟩
  let nw : FKIsingSquareRadialPatchPrimalNode m :=
    ⟨(⟨i + 1, hi1⟩, ⟨j - 1, by omega⟩), by
      change Even ((i + 1) + (j - 1))
      rw [Nat.even_iff]
      have hmod := Nat.even_iff.mp heven
      omega⟩
  let sw : FKIsingSquareRadialPatchPrimalNode m :=
    ⟨(⟨i - 1, by omega⟩, ⟨j - 1, by omega⟩), by
      change Even ((i - 1) + (j - 1))
      rw [Nat.even_iff]
      have hmod := Nat.even_iff.mp heven
      omega⟩
  let se : FKIsingSquareRadialPatchPrimalNode m :=
    ⟨(⟨i - 1, by omega⟩, ⟨j + 1, hj1⟩), by
      change Even ((i - 1) + (j + 1))
      rw [Nat.even_iff]
      have hmod := Nat.even_iff.mp heven
      omega⟩
  have hneighbors :
      (fkIsingSquareRadialPatchPrimalGraph n m hm).neighborFinset c =
        {ne, nw, sw, se} := by
    ext q
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
      Finset.mem_singleton, fkIsingSquareRadialPatchPrimalGraph,
      SimpleGraph.comap_adj]
    change (fkSquareBoxPlanar n).G.Adj
        (fkIsingSquareRadialPatchVertex n m hm
          ⟨i, by omega⟩ ⟨j, by omega⟩)
        (fkIsingSquareRadialPatchPrimalNodeVertex n m hm q) ↔ _
    rw [fkIsingSquareRadialPatch_adj_iff_diagonal
      n m i j hm hi0 hi1 hj0 hj1 heven]
    let embed := fkIsingSquareRadialPatchPrimalNodeVertex n m hm
    have hinj := fkIsingSquareRadialPatchPrimalNodeVertex_injective n m hm
    change (embed q = embed ne ∨ embed q = embed nw ∨
      embed q = embed sw ∨ embed q = embed se) ↔
      q = ne ∨ q = nw ∨ q = sw ∨ q = se
    constructor
    · rintro (h | h | h | h)
      · exact Or.inl (hinj h)
      · exact Or.inr (Or.inl (hinj h))
      · exact Or.inr (Or.inr (Or.inl (hinj h)))
      · exact Or.inr (Or.inr (Or.inr (hinj h)))
    · rintro (rfl | rfl | rfl | rfl) <;> simp
  have hne_nw : ne ≠ nw := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchPrimalNode m ↦ p.1.2.1) h
    simp [ne, nw] at hk
    omega
  have hne_sw : ne ≠ sw := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchPrimalNode m ↦ p.1.1.1) h
    simp [ne, sw] at hk
    omega
  have hne_se : ne ≠ se := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchPrimalNode m ↦ p.1.1.1) h
    simp [ne, se] at hk
    omega
  have hnw_sw : nw ≠ sw := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchPrimalNode m ↦ p.1.1.1) h
    simp [nw, sw] at hk
    omega
  have hnw_se : nw ≠ se := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchPrimalNode m ↦ p.1.1.1) h
    simp [nw, se] at hk
    omega
  have hsw_se : sw ≠ se := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchPrimalNode m ↦ p.1.2.1) h
    simp [sw, se] at hk
  rw [show (⟨(⟨i, by omega⟩, ⟨j, by omega⟩), heven⟩ :
      FKIsingSquareRadialPatchPrimalNode m) = c by rfl]
  unfold isingFiniteGraphLaplacian
  rw [hneighbors]
  simp [hne_nw, hne_sw, hne_se, hnw_sw, hnw_se, hsw_se,
    fkIsingSquareRadialPatchPrimalValue, ne, nw, sw, se]
  unfold fkIsingSquareRadialPatchDiagonalLaplacian
  ring



theorem fkIsingSquareRadialPatchPrimalValue_superharmonicOn
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) :
    IsingFiniteGraphSuperharmonicOn
      (fkIsingSquareRadialPatchPrimalGraph n m hm)
      (fkIsingSquareRadialPatchPrimalBoundary m)
      (fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base) := by
  intro p hp
  have hi0 : 0 < p.1.1.1 := by
    by_contra h
    apply hp
    left
    omega
  have hi1 : p.1.1.1 + 1 < m := by
    have hi := p.1.1.2
    by_contra h
    apply hp
    right; left
    omega
  have hj0 : 0 < p.1.2.1 := by
    by_contra h
    apply hp
    right; right; left
    omega
  have hj1 : p.1.2.1 + 1 < m := by
    have hj := p.1.2.2
    by_contra h
    apply hp
    right; right; right
    omega
  rw [fkIsingSquareRadialPatchPrimalGraph_laplacian_eq_diagonal
    n m p.1.1.1 p.1.2.1 hn hm hmpos base hi0 hi1 hj0 hj1 p.2]
  rw [fkIsingSquareRadialPatchPrimitive_diagonalLaplacian_eq_divergence
      n m p.1.1.1 p.1.2.1 hn hm hmpos hi0 hi1 hj0 hj1 p.2,
    fkIsingSquareRadialPatchPrimalIncrementDivergence_eq_primitiveLaplacian
      n m p.1.1.1 p.1.2.1 hn hm hmpos hi0 hi1 hj0 hj1 p.2]
  apply isingPrimalPrimitiveLaplacian_nonpos_of_rotated_quad
  exact fkIsingSquareRadialPatchFullObservable_quad
    n m p.1.1.1 p.1.2.1 hn hm hi0 hi1 hj0 hj1 p.2


abbrev FKIsingSquareRadialPatchDualNode (m : Nat) :=
  {p : Fin m × Fin m // ¬ Even (p.1.1 + p.2.1)}


def fkIsingSquareRadialPatchDualGraph (m : Nat) :
    SimpleGraph (FKIsingSquareRadialPatchDualNode m) where
  Adj p q :=
    (p.1.1.1 + 1 = q.1.1.1 ∨ q.1.1.1 + 1 = p.1.1.1) ∧
      (p.1.2.1 + 1 = q.1.2.1 ∨ q.1.2.1 + 1 = p.1.2.1)
  symm := by
    intro p q h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := by
    constructor
    intro p h
    rcases h.1 with h | h <;> omega


def fkIsingSquareRadialPatchDualBoundary
    (m : Nat) (p : FKIsingSquareRadialPatchDualNode m) : Prop :=
  p.1.1.1 = 0 ∨ p.1.1.1 + 1 = m ∨
    p.1.2.1 = 0 ∨ p.1.2.1 + 1 = m


def fkIsingSquareRadialPatchDualValue
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (p : FKIsingSquareRadialPatchDualNode m) : Real :=
  base + fkIsingSquareRadialPatchPrimitive
    n m hn hm hmpos p.1.1.1 p.1.2.1



theorem fkIsingSquareRadialPatchDualGraph_laplacian_eq_diagonal
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (hodd : ¬ Even (i + j)) :
    isingFiniteGraphLaplacian (fkIsingSquareRadialPatchDualGraph m)
        (fkIsingSquareRadialPatchDualValue n m hn hm hmpos base)
        ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), hodd⟩ =
      fkIsingSquareRadialPatchDiagonalLaplacian
        (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos) i j := by
  classical
  let c : FKIsingSquareRadialPatchDualNode m :=
    ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), hodd⟩
  let ne : FKIsingSquareRadialPatchDualNode m :=
    ⟨(⟨i + 1, hi1⟩, ⟨j + 1, hj1⟩), by
      change ¬ Even ((i + 1) + (j + 1))
      rw [Nat.not_even_iff]
      have hmod := Nat.not_even_iff.mp hodd
      omega⟩
  let nw : FKIsingSquareRadialPatchDualNode m :=
    ⟨(⟨i + 1, hi1⟩, ⟨j - 1, by omega⟩), by
      change ¬ Even ((i + 1) + (j - 1))
      rw [Nat.not_even_iff]
      have hmod := Nat.not_even_iff.mp hodd
      omega⟩
  let sw : FKIsingSquareRadialPatchDualNode m :=
    ⟨(⟨i - 1, by omega⟩, ⟨j - 1, by omega⟩), by
      change ¬ Even ((i - 1) + (j - 1))
      rw [Nat.not_even_iff]
      have hmod := Nat.not_even_iff.mp hodd
      omega⟩
  let se : FKIsingSquareRadialPatchDualNode m :=
    ⟨(⟨i - 1, by omega⟩, ⟨j + 1, hj1⟩), by
      change ¬ Even ((i - 1) + (j + 1))
      rw [Nat.not_even_iff]
      have hmod := Nat.not_even_iff.mp hodd
      omega⟩
  have hneighbors :
      (fkIsingSquareRadialPatchDualGraph m).neighborFinset c =
        {ne, nw, sw, se} := by
    ext q
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
      Finset.mem_singleton, fkIsingSquareRadialPatchDualGraph]
    change (((i + 1 = q.1.1.1 ∨ q.1.1.1 + 1 = i) ∧
        (j + 1 = q.1.2.1 ∨ q.1.2.1 + 1 = j))) ↔
      q = ne ∨ q = nw ∨ q = sw ∨ q = se
    constructor
    · rintro ⟨hi | hi, hj | hj⟩
      · left
        apply Subtype.ext
        apply Prod.ext <;> apply Fin.ext <;>
          simp [ne] <;> omega
      · right; left
        apply Subtype.ext
        apply Prod.ext <;> apply Fin.ext <;>
          simp [nw] <;> omega
      · right; right; right
        apply Subtype.ext
        apply Prod.ext <;> apply Fin.ext <;>
          simp [se] <;> omega
      · right; right; left
        apply Subtype.ext
        apply Prod.ext <;> apply Fin.ext <;>
          simp [sw] <;> omega
    · rintro (rfl | rfl | rfl | rfl) <;>
        simp [ne, nw, sw, se, c] <;> omega
  have hne_nw : ne ≠ nw := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchDualNode m ↦ p.1.2.1) h
    simp [ne, nw] at hk
    omega
  have hne_sw : ne ≠ sw := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchDualNode m ↦ p.1.1.1) h
    simp [ne, sw] at hk
    omega
  have hne_se : ne ≠ se := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchDualNode m ↦ p.1.1.1) h
    simp [ne, se] at hk
    omega
  have hnw_sw : nw ≠ sw := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchDualNode m ↦ p.1.1.1) h
    simp [nw, sw] at hk
    omega
  have hnw_se : nw ≠ se := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchDualNode m ↦ p.1.1.1) h
    simp [nw, se] at hk
    omega
  have hsw_se : sw ≠ se := by
    intro h
    have hk := congrArg (fun p : FKIsingSquareRadialPatchDualNode m ↦ p.1.2.1) h
    simp [sw, se] at hk
  rw [show (⟨(⟨i, by omega⟩, ⟨j, by omega⟩), hodd⟩ :
      FKIsingSquareRadialPatchDualNode m) = c by rfl]
  unfold isingFiniteGraphLaplacian
  rw [hneighbors]
  simp [hne_nw, hne_sw, hne_se, hnw_sw, hnw_se, hsw_se,
    fkIsingSquareRadialPatchDualValue, ne, nw, sw, se]
  unfold fkIsingSquareRadialPatchDiagonalLaplacian
  ring



theorem fkIsingSquareRadialPatchDualValue_subharmonicOn
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) :
    IsingFiniteGraphSubharmonicOn
      (fkIsingSquareRadialPatchDualGraph m)
      (fkIsingSquareRadialPatchDualBoundary m)
      (fkIsingSquareRadialPatchDualValue n m hn hm hmpos base) := by
  intro p hp
  have hi0 : 0 < p.1.1.1 := by
    by_contra h
    apply hp
    left
    omega
  have hi1 : p.1.1.1 + 1 < m := by
    have hi := p.1.1.2
    by_contra h
    apply hp
    right; left
    omega
  have hj0 : 0 < p.1.2.1 := by
    by_contra h
    apply hp
    right; right; left
    omega
  have hj1 : p.1.2.1 + 1 < m := by
    have hj := p.1.2.2
    by_contra h
    apply hp
    right; right; right
    omega
  rw [fkIsingSquareRadialPatchDualGraph_laplacian_eq_diagonal
    n m p.1.1.1 p.1.2.1 hn hm hmpos base hi0 hi1 hj0 hj1 p.2]
  exact fkIsingSquareRadialPatchPrimitive_diagonalLaplacian_nonneg_of_odd
    n m p.1.1.1 p.1.2.1 hn hm hmpos hi0 hi1 hj0 hj1 p.2



theorem fkIsingSquareRadialPatchPrimalGraph_reachable_boundary
    (n m : Nat) (hm : m ≤ n) :
    ∀ p : FKIsingSquareRadialPatchPrimalNode m, ∃ b,
      fkIsingSquareRadialPatchPrimalBoundary m b ∧
        (fkIsingSquareRadialPatchPrimalGraph n m hm).Reachable p b := by
  let P : Nat → Prop := fun k ↦
    ∀ p : FKIsingSquareRadialPatchPrimalNode m,
      p.1.1.1 + p.1.2.1 = k → ∃ b,
        fkIsingSquareRadialPatchPrimalBoundary m b ∧
          (fkIsingSquareRadialPatchPrimalGraph n m hm).Reachable p b
  suffices ∀ k, P k by
    intro p
    exact this (p.1.1.1 + p.1.2.1) p rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      dsimp only [P]
      intro p hsum
      by_cases hp : fkIsingSquareRadialPatchPrimalBoundary m p
      · exact ⟨p, hp, SimpleGraph.Reachable.refl p⟩
      · have hi0 : 0 < p.1.1.1 := by
          by_contra h
          apply hp
          left
          omega
        have hi1 : p.1.1.1 + 1 < m := by
          have hi := p.1.1.2
          by_contra h
          apply hp
          right; left
          omega
        have hj0 : 0 < p.1.2.1 := by
          by_contra h
          apply hp
          right; right; left
          omega
        have hj1 : p.1.2.1 + 1 < m := by
          have hj := p.1.2.2
          by_contra h
          apply hp
          right; right; right
          omega
        let q : FKIsingSquareRadialPatchPrimalNode m :=
          ⟨(⟨p.1.1.1 - 1, by omega⟩, ⟨p.1.2.1 - 1, by omega⟩), by
            change Even ((p.1.1.1 - 1) + (p.1.2.1 - 1))
            rw [Nat.even_iff]
            have hmod := Nat.even_iff.mp p.2
            omega⟩
        have hqsum : q.1.1.1 + q.1.2.1 < k := by
          simp [q]
          omega
        obtain ⟨b, hb, hqb⟩ := ih _ hqsum q rfl
        refine ⟨b, hb, ?_⟩
        have hpq :
            (fkIsingSquareRadialPatchPrimalGraph n m hm).Adj p q := by
          change (fkSquareBoxPlanar n).G.Adj
            (fkIsingSquareRadialPatchPrimalNodeVertex n m hm p)
            (fkIsingSquareRadialPatchPrimalNodeVertex n m hm q)
          apply (fkIsingSquareRadialPatch_adj_iff_diagonal
            n m p.1.1.1 p.1.2.1 hm hi0 hi1 hj0 hj1 p.2 _).2
          right; right; left
          simp [q, fkIsingSquareRadialPatchPrimalNodeVertex]
        exact hpq.reachable.trans hqb



theorem fkIsingSquareRadialPatchDualGraph_reachable_boundary
    (m : Nat) :
    ∀ p : FKIsingSquareRadialPatchDualNode m, ∃ b,
      fkIsingSquareRadialPatchDualBoundary m b ∧
        (fkIsingSquareRadialPatchDualGraph m).Reachable p b := by
  let P : Nat → Prop := fun k ↦
    ∀ p : FKIsingSquareRadialPatchDualNode m,
      p.1.1.1 + p.1.2.1 = k → ∃ b,
        fkIsingSquareRadialPatchDualBoundary m b ∧
          (fkIsingSquareRadialPatchDualGraph m).Reachable p b
  suffices ∀ k, P k by
    intro p
    exact this (p.1.1.1 + p.1.2.1) p rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      dsimp only [P]
      intro p hsum
      by_cases hp : fkIsingSquareRadialPatchDualBoundary m p
      · exact ⟨p, hp, SimpleGraph.Reachable.refl p⟩
      · have hi0 : 0 < p.1.1.1 := by
          by_contra h
          apply hp
          left
          omega
        have hj0 : 0 < p.1.2.1 := by
          by_contra h
          apply hp
          right; right; left
          omega
        let q : FKIsingSquareRadialPatchDualNode m :=
          ⟨(⟨p.1.1.1 - 1, by omega⟩, ⟨p.1.2.1 - 1, by omega⟩), by
            change ¬ Even ((p.1.1.1 - 1) + (p.1.2.1 - 1))
            rw [Nat.not_even_iff]
            have hmod := Nat.not_even_iff.mp p.2
            omega⟩
        have hqsum : q.1.1.1 + q.1.2.1 < k := by
          simp [q]
          omega
        obtain ⟨b, hb, hqb⟩ := ih _ hqsum q rfl
        refine ⟨b, hb, ?_⟩
        have hpq : (fkIsingSquareRadialPatchDualGraph m).Adj p q := by
          change
            (p.1.1.1 + 1 = q.1.1.1 ∨ q.1.1.1 + 1 = p.1.1.1) ∧
              (p.1.2.1 + 1 = q.1.2.1 ∨ q.1.2.1 + 1 = p.1.2.1)
          constructor <;> right <;> simp [q] <;> omega
        exact hpq.reachable.trans hqb



theorem fkIsingSquareRadialPatchPrimal_harmonic_le_value
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (harmonic : FKIsingSquareRadialPatchPrimalNode m → Real)
    (hharmonic : IsingFiniteGraphHarmonicOn
      (fkIsingSquareRadialPatchPrimalGraph n m hm)
      (fkIsingSquareRadialPatchPrimalBoundary m) harmonic)
    (hboundary : ∀ p, fkIsingSquareRadialPatchPrimalBoundary m p →
      harmonic p ≤
        fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p) :
    ∀ p, harmonic p ≤
      fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p := by
  intro p
  letI : Nonempty (FKIsingSquareRadialPatchPrimalNode m) := ⟨p⟩
  exact isingFiniteGraph_harmonic_le_superharmonic
    (fkIsingSquareRadialPatchPrimalGraph n m hm)
    (fkIsingSquareRadialPatchPrimalBoundary m)
    harmonic (fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base)
    (fkIsingSquareRadialPatchPrimalGraph_reachable_boundary n m hm)
    hharmonic
    (fkIsingSquareRadialPatchPrimalValue_superharmonicOn
      n m hn hm hmpos base)
    hboundary p



theorem fkIsingSquareRadialPatchDual_value_le_harmonic
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (harmonic : FKIsingSquareRadialPatchDualNode m → Real)
    (hharmonic : IsingFiniteGraphHarmonicOn
      (fkIsingSquareRadialPatchDualGraph m)
      (fkIsingSquareRadialPatchDualBoundary m) harmonic)
    (hboundary : ∀ p, fkIsingSquareRadialPatchDualBoundary m p →
      fkIsingSquareRadialPatchDualValue n m hn hm hmpos base p ≤ harmonic p) :
    ∀ p, fkIsingSquareRadialPatchDualValue n m hn hm hmpos base p ≤
      harmonic p := by
  intro p
  letI : Nonempty (FKIsingSquareRadialPatchDualNode m) := ⟨p⟩
  exact isingFiniteGraph_subharmonic_le_harmonic
    (fkIsingSquareRadialPatchDualGraph m)
    (fkIsingSquareRadialPatchDualBoundary m)
    (fkIsingSquareRadialPatchDualValue n m hn hm hmpos base) harmonic
    (fkIsingSquareRadialPatchDualGraph_reachable_boundary m)
    (fkIsingSquareRadialPatchDualValue_subharmonicOn
      n m hn hm hmpos base)
    hharmonic hboundary p



theorem fkIsingSquareRadialPatchPrimitive_horizontal_even_le_odd
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i + 1 < m) (hj : j < m)
    (heven : Even (i + j)) :
    fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j ≤
      fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j := by
  have hinc := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos i j (by omega) (by omega)
  have hnonneg := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i j)
  simp only [fkIsingSquareRadialPatchHorizontalSignedIncrement,
    heven, if_true] at hinc
  linarith



theorem fkIsingSquareRadialPatchPrimitive_horizontal_even_le_odd_of_odd
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i + 1 < m) (hj : j < m)
    (hodd : ¬ Even (i + j)) :
    fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j ≤
      fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j := by
  have hinc := fkIsingSquareRadialPatchPrimitive_horizontal_increment
    n m hn hm hmpos i j (by omega) (by omega)
  have hnonneg := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i j)
  simp only [fkIsingSquareRadialPatchHorizontalSignedIncrement,
    hodd, if_false] at hinc
  linarith


theorem fkIsingSquareRadialPatchPrimitive_vertical_even_le_odd
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j + 1 < m)
    (heven : Even (i + j)) :
    fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j ≤
      fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1) := by
  have hinc := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos i j
  have hnonneg := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i j)
  simp only [fkIsingSquareRadialPatchVerticalSignedIncrement,
    heven, if_true] at hinc
  linarith


theorem fkIsingSquareRadialPatchPrimitive_vertical_even_le_odd_of_odd
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j + 1 < m)
    (hodd : ¬ Even (i + j)) :
    fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1) ≤
      fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j := by
  have hinc := fkIsingSquareRadialPatchPrimitive_vertical_increment
    n m hn hm hmpos i j
  have hnonneg := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i j)
  simp only [fkIsingSquareRadialPatchVerticalSignedIncrement,
    hodd, if_false] at hinc
  linarith




theorem fkIsingSquareRadialPatch_checkerboard_dirichlet_sandwich
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real)
    (primalHarmonic : FKIsingSquareRadialPatchPrimalNode m → Real)
    (dualHarmonic : FKIsingSquareRadialPatchDualNode m → Real)
    (hprimal : IsingFiniteGraphHarmonicOn
      (fkIsingSquareRadialPatchPrimalGraph n m hm)
      (fkIsingSquareRadialPatchPrimalBoundary m) primalHarmonic)
    (hdual : IsingFiniteGraphHarmonicOn
      (fkIsingSquareRadialPatchDualGraph m)
      (fkIsingSquareRadialPatchDualBoundary m) dualHarmonic)
    (hprimalBoundary : ∀ p, fkIsingSquareRadialPatchPrimalBoundary m p →
      primalHarmonic p =
        fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p)
    (hdualBoundary : ∀ p, fkIsingSquareRadialPatchDualBoundary m p →
      dualHarmonic p =
        fkIsingSquareRadialPatchDualValue n m hn hm hmpos base p) :
    (∀ p, primalHarmonic p ≤
      fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p) ∧
      (∀ p, fkIsingSquareRadialPatchDualValue n m hn hm hmpos base p ≤
        dualHarmonic p) := by
  constructor
  · apply fkIsingSquareRadialPatchPrimal_harmonic_le_value
      n m hn hm hmpos base primalHarmonic hprimal
    intro p hp
    exact (hprimalBoundary p hp).le
  · apply fkIsingSquareRadialPatchDual_value_le_harmonic
      n m hn hm hmpos base dualHarmonic hdual
    intro p hp
    exact (hdualBoundary p hp).ge



noncomputable def fkIsingSquareRadialPatchPrimalDirichlet
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) : FKIsingSquareRadialPatchPrimalNode m → Real := by
  letI : Nonempty (FKIsingSquareRadialPatchPrimalNode m) :=
    ⟨⟨(⟨0, hmpos⟩, ⟨0, hmpos⟩), by simp⟩⟩
  exact Classical.choose (isingFiniteGraph_exists_harmonic_extension
    (fkIsingSquareRadialPatchPrimalGraph n m hm)
    (fkIsingSquareRadialPatchPrimalBoundary m)
    (fkIsingSquareRadialPatchPrimalGraph_reachable_boundary n m hm)
    (fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base))

theorem fkIsingSquareRadialPatchPrimalDirichlet_harmonicOn
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) :
    IsingFiniteGraphHarmonicOn
      (fkIsingSquareRadialPatchPrimalGraph n m hm)
      (fkIsingSquareRadialPatchPrimalBoundary m)
      (fkIsingSquareRadialPatchPrimalDirichlet n m hn hm hmpos base) := by
  letI : Nonempty (FKIsingSquareRadialPatchPrimalNode m) :=
    ⟨⟨(⟨0, hmpos⟩, ⟨0, hmpos⟩), by simp⟩⟩
  exact (Classical.choose_spec (isingFiniteGraph_exists_harmonic_extension
    (fkIsingSquareRadialPatchPrimalGraph n m hm)
    (fkIsingSquareRadialPatchPrimalBoundary m)
    (fkIsingSquareRadialPatchPrimalGraph_reachable_boundary n m hm)
    (fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base))).1

theorem fkIsingSquareRadialPatchPrimalDirichlet_boundary
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (p : FKIsingSquareRadialPatchPrimalNode m)
    (hp : fkIsingSquareRadialPatchPrimalBoundary m p) :
    fkIsingSquareRadialPatchPrimalDirichlet n m hn hm hmpos base p =
      fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p := by
  letI : Nonempty (FKIsingSquareRadialPatchPrimalNode m) :=
    ⟨⟨(⟨0, hmpos⟩, ⟨0, hmpos⟩), by simp⟩⟩
  exact (Classical.choose_spec (isingFiniteGraph_exists_harmonic_extension
    (fkIsingSquareRadialPatchPrimalGraph n m hm)
    (fkIsingSquareRadialPatchPrimalBoundary m)
    (fkIsingSquareRadialPatchPrimalGraph_reachable_boundary n m hm)
    (fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base))).2 p hp


noncomputable def fkIsingSquareRadialPatchDualDirichlet
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (base : Real) : FKIsingSquareRadialPatchDualNode m → Real := by
  have hmpos : 0 < m := by omega
  letI : Nonempty (FKIsingSquareRadialPatchDualNode m) :=
    ⟨⟨(⟨0, hmpos⟩, ⟨1, by omega⟩), by norm_num⟩⟩
  exact Classical.choose (isingFiniteGraph_exists_harmonic_extension
    (fkIsingSquareRadialPatchDualGraph m)
    (fkIsingSquareRadialPatchDualBoundary m)
    (fkIsingSquareRadialPatchDualGraph_reachable_boundary m)
    (fkIsingSquareRadialPatchDualValue n m hn hm hmpos base))

theorem fkIsingSquareRadialPatchDualDirichlet_harmonicOn
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (base : Real) :
    IsingFiniteGraphHarmonicOn
      (fkIsingSquareRadialPatchDualGraph m)
      (fkIsingSquareRadialPatchDualBoundary m)
      (fkIsingSquareRadialPatchDualDirichlet n m hn hm hm2 base) := by
  have hmpos : 0 < m := by omega
  letI : Nonempty (FKIsingSquareRadialPatchDualNode m) :=
    ⟨⟨(⟨0, hmpos⟩, ⟨1, by omega⟩), by norm_num⟩⟩
  exact (Classical.choose_spec (isingFiniteGraph_exists_harmonic_extension
    (fkIsingSquareRadialPatchDualGraph m)
    (fkIsingSquareRadialPatchDualBoundary m)
    (fkIsingSquareRadialPatchDualGraph_reachable_boundary m)
    (fkIsingSquareRadialPatchDualValue n m hn hm hmpos base))).1

theorem fkIsingSquareRadialPatchDualDirichlet_boundary
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (base : Real) (p : FKIsingSquareRadialPatchDualNode m)
    (hp : fkIsingSquareRadialPatchDualBoundary m p) :
    fkIsingSquareRadialPatchDualDirichlet n m hn hm hm2 base p =
      fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base p := by
  have hmpos : 0 < m := by omega
  letI : Nonempty (FKIsingSquareRadialPatchDualNode m) :=
    ⟨⟨(⟨0, hmpos⟩, ⟨1, by omega⟩), by norm_num⟩⟩
  exact (Classical.choose_spec (isingFiniteGraph_exists_harmonic_extension
    (fkIsingSquareRadialPatchDualGraph m)
    (fkIsingSquareRadialPatchDualBoundary m)
    (fkIsingSquareRadialPatchDualGraph_reachable_boundary m)
    (fkIsingSquareRadialPatchDualValue n m hn hm hmpos base))).2 p hp



theorem fkIsingSquareRadialPatch_constructed_dirichlet_sandwich
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (base : Real) :
    (∀ p, fkIsingSquareRadialPatchPrimalDirichlet
        n m hn hm (by omega) base p ≤
      fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p) ∧
      (∀ p, fkIsingSquareRadialPatchDualValue
          n m hn hm (by omega) base p ≤
        fkIsingSquareRadialPatchDualDirichlet n m hn hm hm2 base p) := by
  apply fkIsingSquareRadialPatch_checkerboard_dirichlet_sandwich
    n m hn hm (by omega) base
    (fkIsingSquareRadialPatchPrimalDirichlet n m hn hm (by omega) base)
    (fkIsingSquareRadialPatchDualDirichlet n m hn hm hm2 base)
    (fkIsingSquareRadialPatchPrimalDirichlet_harmonicOn
      n m hn hm (by omega) base)
    (fkIsingSquareRadialPatchDualDirichlet_harmonicOn
      n m hn hm hm2 base)
  · exact fkIsingSquareRadialPatchPrimalDirichlet_boundary
      n m hn hm (by omega) base
  · exact fkIsingSquareRadialPatchDualDirichlet_boundary
      n m hn hm hm2 base

end

end StatMech.Universality
