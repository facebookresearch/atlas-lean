/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.EdwardsSokal

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.EdwardsSokal`

On the one-edge graph `⊤ : SimpleGraph (Fin 2)` with `q = 2` or `q = 3` colors:
* `esEdgeFactor` is `p` on an open monochromatic edge, `0` on an open bichromatic edge and
  `1 - p` on a closed edge;
* `esWeight` (the Edwards–Sokal joint weight) is `p` for the open edge with a constant coloring and
  `0` for the open edge with the coloring `i ↦ i`;
* `ConstOnOpen` holds for a constant coloring and fails for `i ↦ i` when the edge is open, and holds
  for every coloring when all edges are closed;
* `esZ_eq_fkZ`: the joint partition function is the random-cluster partition function;
* the marginals: `esSecondMarginal` is the random-cluster measure and sums to `1`, and
  `esFirstMarginal` at `p = 1 - e^{-βJ}` is the Potts measure and sums to `1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.EdwardsSokal

open _root_.StatMech _root_.StatMech.FK

/-- The configuration with every coordinate open. -/
def allOpen : ConfigSpace (Sym2 (Fin 2)) := fun _ => true

/-- The configuration with every coordinate closed. -/
def allClosed : ConfigSpace (Sym2 (Fin 2)) := fun _ => false

/-- The constant coloring `0` on `Fin 2` with `q` colors. -/
def constSpin (q : ℕ) [NeZero q] : Fin 2 → Fin q := fun _ => 0

/-- The non-constant coloring `i ↦ i` on `Fin 2` with two colors. -/
def idSpin : Fin 2 → Fin 2 := fun i => i

/-- The edge set of `⊤ : SimpleGraph (Fin 2)` is the single edge `s(0, 1)`. -/
theorem edgeFinset_top_fin2 : (⊤ : SimpleGraph (Fin 2)).edgeFinset = {s(0, 1)} := by
  ext e
  induction e with
  | _ x y => fin_cases x <;> fin_cases y <;> simp

-- An open monochromatic edge has factor `p`.
example (p : ℝ) : esEdgeFactor p (constSpin 3) allOpen s(0, 1) = p := by
  simp [esEdgeFactor, allOpen, constSpin]

-- An open bichromatic edge has factor `0`: open edges force agreement.
example (p : ℝ) : esEdgeFactor p idSpin allOpen s(0, 1) = 0 := by
  simp [esEdgeFactor, allOpen, idSpin]

-- A closed edge has factor `1 - p` whatever the colors.
example (p : ℝ) (σ : Fin 2 → Fin 3) : esEdgeFactor p σ allClosed s(0, 1) = 1 - p := by
  simp [esEdgeFactor, allClosed]

-- The joint weight of the open edge with a constant coloring is `p`.
example (p : ℝ) : esWeight (⊤ : SimpleGraph (Fin 2)) p (constSpin 2) allOpen = p := by
  rw [esWeight, edgeFinset_top_fin2, Finset.prod_singleton]
  simp [esEdgeFactor, allOpen, constSpin]

-- The joint weight of the open edge with the coloring `i ↦ i` is `0`.
example (p : ℝ) : esWeight (⊤ : SimpleGraph (Fin 2)) p idSpin allOpen = 0 := by
  rw [esWeight, edgeFinset_top_fin2, Finset.prod_singleton]
  simp [esEdgeFactor, allOpen, idSpin]

-- A constant coloring is constant on open clusters.
example : ConstOnOpen (⊤ : SimpleGraph (Fin 2)) allOpen (constSpin 3) :=
  fun _ _ _ => rfl

-- The coloring `i ↦ i` is not constant on the open edge `{0, 1}`.
example : ¬ ConstOnOpen (⊤ : SimpleGraph (Fin 2)) allOpen idSpin := by
  intro h
  have := h 0 1 (by simp [allOpen])
  simp [idSpin] at this

-- With every edge closed, every coloring is constant on open clusters.
example (σ : Fin 2 → Fin 2) : ConstOnOpen (⊤ : SimpleGraph (Fin 2)) allClosed σ := by
  intro x y h
  simp [allClosed] at h

-- The joint partition function equals the random-cluster partition function.
example (p : ℝ) : esZ (⊤ : SimpleGraph (Fin 2)) 3 p = fkZ (⊤ : SimpleGraph (Fin 2)) p 3 := by
  simpa using esZ_eq_fkZ (⊤ : SimpleGraph (Fin 2)) 3 p

-- The bond marginal is the random-cluster measure (`p = 1/2`, `q = 2`) and sums to one.
example (ω : ConfigSpace (Sym2 (Fin 2))) :
    esSecondMarginal (⊤ : SimpleGraph (Fin 2)) 2 (1 / 2) ω
      = fkProb (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 ω := by
  simpa using esSecondMarginal_eq_fkProb (⊤ : SimpleGraph (Fin 2)) 2 (1 / 2) ω

-- The bond marginal sums to one.
example : ∑ ω, esSecondMarginal (⊤ : SimpleGraph (Fin 2)) 2 (1 / 2) ω = 1 :=
  esSecondMarginal_sum_eq_one _ (by norm_num) (by norm_num) (by norm_num)

-- The spin marginal at `p = 1 - e^{-βJ}` is the Potts measure (`β = J = 1`, `q = 3`).
example (σ : Fin 2 → Fin 3) :
    esFirstMarginal (⊤ : SimpleGraph (Fin 2)) 3 (1 - Real.exp (-(1 * 1))) σ
      = Potts.pottsProb (⊤ : SimpleGraph (Fin 2)) 3 1 1 σ :=
  edwardsSokal_firstMarginal _ 3 1 1 σ

-- The spin marginal sums to one.
example : ∑ σ : Fin 2 → Fin 3,
    esFirstMarginal (⊤ : SimpleGraph (Fin 2)) 3 (1 - Real.exp (-(1 * 1))) σ = 1 :=
  esFirstMarginal_sum_eq_one _ 1 1

-- The bond marginal of the joint measure at `β = J = 1` is the random-cluster measure.
example (ω : ConfigSpace (Sym2 (Fin 2))) :
    esSecondMarginal (⊤ : SimpleGraph (Fin 2)) 3 (1 - Real.exp (-(1 * 1))) ω
      = fkProb (⊤ : SimpleGraph (Fin 2)) (1 - Real.exp (-(1 * 1))) (3 : ℕ) ω :=
  edwardsSokal_secondMarginal _ 3 1 1 ω

end PhyslibExtTest.StatisticalMechanics.RandomCluster.EdwardsSokal
