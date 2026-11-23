/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Two-sided paving with O(ε⁻²) blocks (Oberwolfach Reports 17/2015)

Oberwolfach Arbeitsgemeinschaft The Kadison-Singer Conjecture (2015), problem session, A. Marcus,
Problem 4(4): paving within `ε` is known with `O(ε⁻⁴)` blocks, because the top and bottom
eigenvalues are bounded by two separate partitions, against the lower bound `Ω(ε⁻²)`; can both sides
of the paving bound be obtained at once?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.CStarAlgebra.KadisonSinger

@[expose] public section

namespace MathlibExt.LinearAlgebra.TwoSidedPavingQuadraticOWR13674Problem020Wanted

/-!
Source: A. Marcus, in Arbeitsgemeinschaft: The Kadison-Singer Conjecture, Oberwolfach Reports 12
(2015), no. 17, pp. 965-966, Problem 4(4), DOI 10.4171/OWR/2015/17. UnsolvedMath record UM-30002849
(`OWR-13674-020`), dataset ulamai/UnsolvedMath v1.8.0.

The question is read as asking for two-sided pavings with `O(ε⁻²)` blocks, matching the lower bound
the source quotes: a constant `C` and, for every Hermitian zero-diagonal contraction `A`, a
partition into at most `C ε⁻²` blocks `S` with `‖P_S A P_S‖ ≤ ε`. Matrix norms are operator norms
(`Matrix.Norms.L2Operator`) and `P_S` is MathlibExt's `pavingProj`, as in `kadison_singer_paving`,
which proves paving without a rate; blocks may be empty.
-/

open scoped Matrix.Norms.L2Operator
open MathlibExt.Analysis.CStarAlgebra.KadisonSingerWanted (pavingProj)

/-- Two-sided paving with `O(ε⁻²)` blocks (Oberwolfach Report 17/2015, Problem 4(4)): there is a
constant `C` such that for every `ε ∈ (0, 1)`, every Hermitian `n × n` matrix `A` with zero
diagonal and operator norm at most `1` has a partition of its index set into at most `C ε⁻²`
blocks `S` with `‖P_S A P_S‖ ≤ ε` (operator norm; `P_S` is MathlibExt's `pavingProj`). -/
def twoSidedPavingQuadratic : Prop :=
  ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.IsHermitian → (∀ i, A i i = 0) → ‖A‖ ≤ 1 →
      ∃ (r : ℕ) (c : Fin n → Fin r), (r : ℝ) ≤ C / ε ^ 2 ∧
        ∀ j, ‖pavingProj n r c j * A * pavingProj n r c j‖ ≤ ε

/--
Resolved true: Ravichandran and Srivastava pave `k` zero-diagonal Hermitian contractions
simultaneously with at most `18 k ε⁻²` blocks so that every block has top eigenvalue below `ε`; they
conclude that zero-diagonal contractions can be `(O(ε⁻²), ε)` paved (applied to `A` and `-A`, both
sides are bounded by one partition). Source: A. Marcus, in Arbeitsgemeinschaft: The Kadison-Singer
Conjecture, Oberwolfach Reports 12 (2015), no. 17, pp. 965-966, Problem 4(4), DOI
10.4171/OWR/2015/17; resolution: M. Ravichandran and N. Srivastava, Asymptotically optimal
multi-paving, Int. Math. Res. Not. IMRN 2021, arXiv:1706.03737, abstract and Theorem 1:
zero-diagonal Hermitian contractions A^(1), ..., A^(k) have a common paving into r ≤ 18 k ε⁻² blocks
with λ_max(P_X A^(j) P_X) < ε; consequently zero-diagonal contractions can be (O(ε⁻²), ε) paved,
https://arxiv.org/abs/1706.03737.
-/
public theorem_wanted twoSidedPavingQuadratic_holds : twoSidedPavingQuadratic

end MathlibExt.LinearAlgebra.TwoSidedPavingQuadraticOWR13674Problem020Wanted
