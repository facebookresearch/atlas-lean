/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Jerrum-Sinclair-Vigoda: FPRAS for the permanent

Source:
M. Jerrum, A. Sinclair, and E. Vigoda, "A polynomial-time approximation algorithm
for the permanent of a matrix with nonnegative entries", Journal of the ACM 51 (2004),
671-697 (Proceedings of the Thirty-Third Annual ACM Symposium on Theory of Computing,
STOC 2001, 165-171); M. Jerrum and A. Sinclair, "Approximating the permanent", SIAM
Journal on Computing 18 (1989), 1149-1178 (precursor with restricted guarantees).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.JerrumSinclairVigoda

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Jerrum-Sinclair-Vigoda: FPRAS for the permanent

The permanent of a 0-1 matrix (equivalently, the number of perfect matchings of a bipartite
graph) admits a fully polynomial randomized approximation scheme (FPRAS): a single
polynomial-time estimator `Est` takes the instance, a random string, and the precision
parameter in unary (a bitstring `prec` of length `n`, so `|prec| = n`), and outputs an
estimate within a multiplicative `(1 ± 1/n)` factor of the true permanent with probability
at least `2/3`. The number of random bits and the estimator's running time are polynomial
in `|x| + n` (the precision is unary, so polynomial time in the input length is polynomial
in `|x| + n`); a separate hard-coded estimator per precision would be nonuniform and
would not be an FPRAS. The general FPRAS, including the 0-1 case formalized here,
is due to Jerrum, Sinclair, and Vigoda (Markov chains on matchings with a weighting
scheme, applied to matrices with nonnegative entries); the 1989 Jerrum-Sinclair paper
was a precursor with restricted guarantees and did not provide an FPRAS for
arbitrary 0-1 permanents. The input decodes to `(dimension, row-major entries)` with
entries in `{0, 1}`; malformed inputs have permanent `0`.
-/

/-- The permanent of the 0-1 matrix decoded from `x` (`0` on malformed inputs). -/
noncomputable def permOf (x : List Bool) : ℕ :=
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := ℕ × List ℕ) x with
  | some (n, entries) =>
    if entries.length = n * n ∧ ∀ e ∈ entries, e ≤ 1 then
      (Finset.univ : Finset (Equiv.Perm (Fin n))).sum (fun σ =>
        (Finset.univ : Finset (Fin n)).prod
          (fun i => entries.getD (i.val * n + (σ i).val) 0))
    else 0
  | none => 0

/-- **Jerrum-Sinclair-Vigoda: FPRAS for the permanent.** Source: M. Jerrum, A. Sinclair,
and E. Vigoda, "A polynomial-time approximation algorithm for the permanent of a matrix
with nonnegative entries", Journal of the ACM 51 (2004), 671-697 (STOC 2001); M. Jerrum
and A. Sinclair, "Approximating the permanent", SIAM Journal on Computing 18 (1989),
1149-1178 (precursor with restricted guarantees). -/
public theorem_wanted jerrum_sinclair_vigoda_permanent :
    ∃ p : Polynomial ℕ, ∃ Est : List Bool × List Bool × List Bool → ℕ,
      IsPolyTime Est ∧ ∀ (x : List Bool) (prec : List Bool), 1 ≤ prec.length →
        3 * Set.ncard {r : Fin (p.eval (x.length + prec.length)) → Bool |
          |(Est (x, List.ofFn r, prec) : ℚ) - (permOf x : ℚ)| ≤
            (permOf x : ℚ) / (prec.length : ℚ)} ≥
          2 * 2 ^ (p.eval (x.length + prec.length))

end MetaMathlibExt.Complexity.KeyTheorems.JerrumSinclairVigoda
