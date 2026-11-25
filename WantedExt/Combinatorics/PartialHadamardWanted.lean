/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.PartialHadamard

@[expose] public section

namespace MathlibExt.Combinatorics.PartialHadamardWanted

open MathlibExt.Combinatorics.PartialHadamard

/-!
# The cubic threshold for the partial Hadamard leading term

Both directions of the exact leading-term threshold recorded by
Optimization Problems 23c, as proof requests. The catalogue constant
`C_{23c}` itself (corrected formulas below the cubic scale) is not
formalized; see the model scope note.
-/

/-- **Partial Hadamard counts follow the leading term above the cubic scale.** The exponent $3$ is
admissible for the partial Hadamard leading term. That is, let $N_{n,m}$ be the number of
$n \times m$ partial Hadamard matrices and let
$A_{n,4t} = 2^{4nt + (n-1)^2} (8\pi t)^{-n(n-1)/4}$ be the de Launey–Levin leading term. Then for
all sequences $(n_k)$ and $(t_k)$ of natural numbers with $n_k \ge 2$ for every $k$ and
$t_k / n_k^3 \to \infty$ as $k \to \infty$, the ratio $N_{n_k, 4t_k} / A_{n_k, 4t_k}$ tends to $1$.

Source: Davis, *Counting partial Hadamard matrices in the cubic
regime*, arXiv:2603.30013 (2026): the leading term is asymptotic in
the regime `t / n³ → ∞`. Known literature result (preprint); its
proof is not supplied here. -/
theorem_wanted davisCubicAdmissible_wanted :
    IsLeadingAdmissible 3

/-- **No exponent below 3 is admissible for the partial Hadamard leading term.** Let $N_{n,m}$ be
the number of $n \times m$ partial Hadamard matrices and let
$A_{n,4t} = 2^{4nt + (n-1)^2} (8\pi t)^{-n(n-1)/4}$ be the de Launey–Levin leading term. Then for
every real number $\alpha < 3$ there are sequences $(n_k)$ and $(t_k)$ of natural numbers with
$n_k \ge 2$ for every $k$ and $t_k / n_k^{\alpha} \to \infty$ as $k \to \infty$ along which the
ratio $N_{n_k, 4t_k} / A_{n_k, 4t_k}$ does not tend to $1$.

Source: Davis (2026), same paper: a nonvanishing correction at
`t = Θ n³` for large fixed `Θ` blocks every smaller exponent for the
leading term alone. Known literature result (preprint); its proof is
not supplied here. -/
theorem_wanted davisCubicSharp_wanted :
    ∀ α : ℝ, α < 3 → ¬ IsLeadingAdmissible α

end MathlibExt.Combinatorics.PartialHadamardWanted
