/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.RSW.Defs

/-!
# Equivalent forms of the box-crossing property (abstract implications)

In the Duminil-Copin–Tassion approach to RSW theory, the box-crossing property `P5` (crossings of
`αn × n` boxes have probability bounded below uniformly in `n`) is equivalent to:

* `P5a`: open circuits in the annulus `Λ_{2n} \ Λ_n` have probability bounded below;
* `P5b`: the same, uniformly over boundary conditions on annuli of every ratio `R ≥ 2`;
* `P5c`: two-sided crossing bounds uniform over a family of measures.

This file proves the *propositional skeleton* of these equivalences for abstract set functions
`μ n`, `ν R n : Set Ω → ℝ`. Each implication takes the comparison it needs as a hypothesis; none
of the percolation geometry (FKG gluing of crossings into circuits, comparison of boundary
conditions) is proved here.

## Main definitions

* `StatMech.RSW.Box.annulusEvent`: open circuit in `Λ_{2n} \ Λ_n` around the origin.
* `StatMech.RSW.Box.rp5_P5a`, `StatMech.RSW.Box.rp5_P5b`: the annulus-circuit forms.

## Main results

* `StatMech.RSW.Box.rp5_p5_p5a`: `P5 → P5a`, given a gluing bound.
* `StatMech.RSW.Box.rp5_p5a_p5b`: `P5a → P5b`, given a boundary-condition comparison.
* `StatMech.RSW.Box.rp5_p5b_p5_upper`: an upper crossing bound from a lower bound on the
  complementary quantity.

No `P5 ↔ P5c` component is claimed: the two-sided form `P5c` is defined in `Defs`, and
`P5c.p5` gives `P5c → P5`, but an equivalence would need non-circular comparison hypotheses,
which are not proved here.

## Implementation notes

The `P5b → P5` step and the combined equivalence `rp5_p5_equiv` were removed: they needed a
hypothesis `hchain` asking for one bound `ν 2 n (annulusEvent n) ≤ μ n (boxCrossingEvent α n)`
valid for *every* `α`. For a genuine Bernoulli measure with `0 < p < 1` and fixed `n ≥ 1`, the
crossing probability of `[0, ⌊αn⌋] × [0, n]` tends to `0` as `α → ∞`, so `hchain` then forces
`ν 2 n (annulusEvent n) ≤ 0`. Thus `hchain` is not satisfied by the intended percolation quantities
(the literature constant depends on `α`); the removed results were meaningful only for abstract
set functions. This is argued by hand, not proved in Lean.

## References

* H. Duminil-Copin, V. Tassion, *RSW and box-crossing property for planar percolation*,
  Proceedings of the International Congress of Mathematical Physics (2015).
* V. Tassion, *Crossing probabilities for Voronoi percolation*, Ann. Probab. 44 (2016), 3385–3398.
-/

@[expose] public section

open Set

namespace StatMech

namespace RSW

namespace Box

open StatMech.Lattice
open StatMech.TwoDim

/-- The event that there is an open circuit in the annulus `Λ_{2n} \ Λ_n` around the origin. -/
def annulusEvent (n : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  annulusCircuitEvent (fun _ => 0) n

@[simp] theorem mem_annulusEvent {n : ℕ} {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ annulusEvent n ↔ AnnulusCircuit ω (fun _ => 0) n := Iff.rfl

/-- Property `P5a`: annulus circuits have probability bounded below uniformly in `n`. -/
def rp5_P5a (μ : ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c ≤ μ n (annulusEvent n)

/-- Property `P5b`: for every ratio `R ≥ 2`, annulus circuits have `ν R n`-probability bounded
below uniformly in `n` (in the literature `ν R n` is the worst boundary condition on `Λ_{Rn}`). -/
def rp5_P5b (ν : ℕ → ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ) : Prop :=
  ∀ R : ℕ, 2 ≤ R → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c ≤ ν R n (annulusEvent n)

/-- `P5a → P5b`, given the comparison `μ n (annulus) ≤ ν R n (annulus)` for all `R`. -/
theorem rp5_p5a_p5b
    {μ : ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
    {ν : ℕ → ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
    (hcmp : ∀ R n : ℕ, μ n (annulusEvent n) ≤ ν R n (annulusEvent n))
    (h : rp5_P5a μ) : rp5_P5b ν := by
  obtain ⟨c, hc, hμ⟩ := h
  intro R _hR
  refine ⟨c, hc, fun n => ?_⟩
  exact (hμ n).trans (hcmp R n)

/-- `P5 → P5a`, given the gluing bound `μ n (box crossing, ratio 10)^4 ≤ μ n (annulus)` (in the
literature: four crossings of long boxes glued by FKG form a circuit). -/
theorem rp5_p5_p5a
    {μ : ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
    (hglue : ∀ n : ℕ,
      (μ n (boxCrossingEvent 10 n)) ^ 4 ≤ μ n (annulusEvent n))
    (h : P5 μ) : rp5_P5a μ := by
  obtain ⟨c, hc, hμ⟩ := h 10 (by norm_num)
  refine ⟨c ^ 4, by positivity, fun n => ?_⟩
  refine le_trans ?_ (hglue n)
  have hcle : c ≤ μ n (boxCrossingEvent 10 n) := hμ n
  exact pow_le_pow_left₀ hc.le hcle 4

/-- Upper crossing bound from a lower bound on the complementary quantity: if
`μ n (B) + compl n (B) = 1` and `compl n (B) ≥ c`, then `μ n (B) ≤ 1 - c`. -/
theorem rp5_p5b_p5_upper
    {μ : ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
    {compl : ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
    {α : ℝ} {c : ℝ} (_hc : 0 < c)
    (hnorm : ∀ n : ℕ,
      μ n (boxCrossingEvent α n) + compl n (boxCrossingEvent α n) = 1)
    (hdual : ∀ n : ℕ, c ≤ compl n (boxCrossingEvent α n)) :
    ∀ n : ℕ, μ n (boxCrossingEvent α n) ≤ 1 - c := by
  intro n
  have h := hnorm n
  have hd := hdual n
  linarith

end Box

end RSW

end StatMech
