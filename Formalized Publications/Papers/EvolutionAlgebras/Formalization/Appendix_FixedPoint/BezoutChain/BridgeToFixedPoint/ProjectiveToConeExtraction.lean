/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Projective-to-cone extraction (T7, catenary-independent part)

From a projective point `q ∈ vanishingLocus n K G` with
`q ≠ distinguishedPoint n K`, produce affine-cone data: a nonzero
representative `v` (hence an `(X, z)` pair splitting `v` along
`Fin.castSucc` / `Fin.last`) satisfying the cone equations
`MvPolynomial.eval v (G i) = 0` for all `i`, with the `x`-part `X ≠ 0`.

Pure projective-linear algebra: needs nothing from unmixedness, catenary,
avoidance, or counting. The key step is the contrapositive: a representative
with `X = 0` is a nonzero scalar multiple of `zRep`, hence classifies as
`distinguishedPoint`.

## Adjustment vs plan T7

The T7 task phrases the cone equations as `∀ k, homogQuadric K c k X z = 0`
(the `homogQuadric` shape that `fixedPoint_fromBezout` consumes). That form needs
the T1 polynomial embedding (structure constants `c`, `sqCoords`,
`homogQuadric`, the `mkSystem` eval-bridge), which is out of scope for this
standalone file. We prove the polynomial-level version
`∀ i, MvPolynomial.eval w (G i) = 0` on the combined vector
`w = Fin.lastCases z X`; T1's eval-bridge turns it into the `homogQuadric`
form. The `X ≠ 0` output shape is exactly as downstream steps 4-5 require.

## T5 verdict

skipped (not statable without hard inputs): T5 asks
to prove `IsZeroDimensional` or thread the `hZd` / `¬hZd` case split via
`Counting.infinite_locus_of_not_zeroDim` (`hcontra`). Both branches need the
corollary/counting inputs (`hZd`, `hcontra` from the `CountingHandoff` G-contra
gap, `ℓ` / `hreg` from R1, `hloc` locality) — none follow from
projective-linear algebra alone, and staging them as open hypotheses is
forbidden. No T5 content is attempted here.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`, `vanishingLocus`,
  `distinguishedPoint`, `zRep`, `zRep_ne_zero`.
* `Mathlib/LinearAlgebra/Projectivization/Basic.lean`, `Projectivization.mk`,
  `Projectivization.mk_eq_mk_iff'`, `Projectivization.rep`,
  `Projectivization.rep_nonzero`, `Projectivization.mk_rep`.
* Lean core, `Fin.lastCases`, `Fin.lastCases_last`, `Fin.lastCases_castSucc`,
  `Fin.castSucc_lt_last`, `Pi.single_eq_same`, `Pi.single_eq_of_ne`.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-! ## The distinguished axis vanishes on `x`-coordinates -/

/-- `zRep` vanishes on the `x`-coordinates (the `Fin.castSucc` range).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`, `zRep`.
* Lean core, `Pi.single_eq_of_ne`, `Fin.castSucc_lt_last`. -/
theorem zRep_castSucc_eq_zero (n : ℕ) (K : Type*) [Field K] (i : Fin (n + 1)) :
    zRep n K (Fin.castSucc i) = 0 := by
  unfold zRep
  exact Pi.single_eq_of_ne (Fin.castSucc_lt_last i).ne 1

/-! ## Contrapositive: vanishing `x`-part classifies the point -/

/-- Key contrapositive for T7: a representative whose `x`-part vanishes
classifies as the distinguished point (it is a nonzero multiple of `zRep`).
Proof idea: the representative equals its `z`-coordinate times `zRep`
(checked coordinate-wise by `Fin.lastCases`), so `mk_eq_mk_iff'`
identifies the two projective points.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `distinguishedPoint`, `zRep`,
  `zRep_ne_zero`.
* `Mathlib/LinearAlgebra/Projectivization/Basic.lean`,
  `Projectivization.mk_eq_mk_iff'`.
* Lean core, `Fin.lastCases`, `Pi.single_eq_same`. -/
theorem mk_eq_distinguishedPoint_of_castSucc_eq_zero (n : ℕ) (K : Type*)
    [Field K] (v : Fin (n + 2) → K) (hv : v ≠ 0)
    (hX : (fun i : Fin (n + 1) => v (Fin.castSucc i)) = 0) :
    Projectivization.mk K v hv = distinguishedPoint n K := by
  have hXi : ∀ i : Fin (n + 1), v (Fin.castSucc i) = 0 := fun i => congrFun hX i
  have hscale : v (Fin.last (n + 1)) • zRep n K = v := by
    funext j
    refine Fin.lastCases
      (motive := fun j => (v (Fin.last (n + 1)) • zRep n K) j = v j) ?_ ?_ j
    · simp only [zRep, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one]
    · intro i
      have hzr : zRep n K (Fin.castSucc i) = 0 := zRep_castSucc_eq_zero n K i
      rw [Pi.smul_apply, smul_eq_mul, hzr, mul_zero]
      exact (hXi i).symm
  have hmk : Projectivization.mk K v hv
      = Projectivization.mk K (zRep n K) (zRep_ne_zero n K) := by
    rw [Projectivization.mk_eq_mk_iff']
    exact ⟨v (Fin.last (n + 1)), hscale⟩
  exact hmk

/-! ## Rep-level extraction -/

/-- T7 rep-level extraction: a locus point distinct from the distinguished
point has a nonzero representative satisfying every cone equation whose
`x`-part is nonzero.
Proof idea: take the canonical representative `q.rep`; the cone equations
hold by `hmem` at that representative, and the `x`-part is nonzero by
the contrapositive above (else `q` would be the distinguished point).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`, `vanishingLocus`,
  `distinguishedPoint`.
* `Mathlib/LinearAlgebra/Projectivization/Basic.lean`,
  `Projectivization.rep`, `Projectivization.rep_nonzero`,
  `Projectivization.mk_rep`. -/
theorem exists_rep_of_mem_ne_distinguishedPoint (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (q : Projectivization K (Fin (n + 2) → K))
    (hmem : q ∈ vanishingLocus n K G)
    (hne : q ≠ distinguishedPoint n K) :
    ∃ (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = q ∧
        (∀ i, MvPolynomial.eval v (G i) = 0) ∧
        (fun i : Fin (n + 1) => v (Fin.castSucc i)) ≠ 0 := by
  refine ⟨q.rep, q.rep_nonzero, Projectivization.mk_rep q, ?_, ?_⟩
  · intro i
    exact hmem q.rep q.rep_nonzero (Projectivization.mk_rep q) i
  · intro hcon
    apply hne
    rw [← Projectivization.mk_rep q]
    exact mk_eq_distinguishedPoint_of_castSucc_eq_zero n K q.rep q.rep_nonzero
      hcon

/-! ## Cone-pair extraction -/

/-- T7 standalone extraction lemma (polynomial-level cone equations): a locus
point distinct from the distinguished point yields cone data
`(X, z) : (Fin (n + 1) → K) × K` whose combined vector
`Fin.lastCases z X` is a nonzero representative of `q` satisfying every cone
equation, with `X ≠ 0` (the exact output shape downstream steps 4-5 require).
Proof idea: split the rep-level vector from the previous lemma along
`Fin.lastCases` and rewrite; the combined vector is `v` itself.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`, `vanishingLocus`,
  `distinguishedPoint`.
* Lean core, `Fin.lastCases`. -/
theorem exists_conePair_of_mem_ne_distinguishedPoint (n : ℕ) (K : Type*)
    [Field K] (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (q : Projectivization K (Fin (n + 2) → K))
    (hmem : q ∈ vanishingLocus n K G)
    (hne : q ≠ distinguishedPoint n K) :
    ∃ (X : Fin (n + 1) → K) (z : K),
      (∃ hw : Fin.lastCases (motive := fun _ => K) z X ≠ 0,
        Projectivization.mk K (Fin.lastCases (motive := fun _ => K) z X) hw
          = q) ∧
      (∀ i, MvPolynomial.eval (Fin.lastCases (motive := fun _ => K) z X) (G i)
        = 0) ∧
      X ≠ 0 := by
  obtain ⟨v, hv, hmk, heval, hX⟩ :=
    exists_rep_of_mem_ne_distinguishedPoint n K G q hmem hne
  have hcomb : Fin.lastCases (motive := fun _ => K) (v (Fin.last (n + 1)))
      (fun i => v (Fin.castSucc i)) = v := by
    funext j
    refine Fin.lastCases (motive := fun j =>
      Fin.lastCases (motive := fun _ => K) (v (Fin.last (n + 1)))
        (fun i => v (Fin.castSucc i)) j = v j) ?_ ?_ j
    · simp
    · intro i
      simp
  refine ⟨fun i => v (Fin.castSucc i), v (Fin.last (n + 1)), ?_, ?_, hX⟩
  · rw [hcomb]
    exact ⟨hv, hmk⟩
  · rw [hcomb]
    exact heval

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
