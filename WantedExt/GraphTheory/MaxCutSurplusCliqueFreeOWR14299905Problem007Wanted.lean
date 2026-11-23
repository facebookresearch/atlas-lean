/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# An absolute exponent for the MaxCut surplus of K_r-free graphs (Oberwolfach Report 1/2026)

A. Milojević (with Z. Jin, I. Tomon and S. Zhang), MaxCut in H-free graphs: recent results and
connections, Oberwolfach Report 1/2026, pp. 13-14: is there an absolute `ε > 0` such that every
`K_r`-free graph with `m` edges has surplus `Ω_r(m^{1/2 + ε})`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MathlibExt.GraphTheory.MaxCutSurplusCliqueFreeOWR14299905Problem007Wanted

/-!
Source: A. Milojević (with Z. Jin, I. Tomon and S. Zhang), MaxCut in H-free graphs: recent results
and connections, in Combinatorics, Oberwolfach Reports 23 (2026), no. 1, pp. 13-14, DOI
10.4171/OWR/2026/1. UnsolvedMath record UM-30006540 (`OWR-14299905-007`), dataset
ulamai/UnsolvedMath v1.8.0.

The surplus is `surp(G) = mc(G) - m/2`, `mc(G)` the maximum number of edges crossing a bipartition.
`Ω_r(m^{1/2 + ε})` is read as: every `K_r`-free `G` has a vertex set `S` with at least `m/2 + c_r
m^{1/2 + ε}` edges between `S` and its complement, i.e. `mc(G) ≥ m/2 + c_r m^{1/2 + ε}`, with `c_r >
0` depending on `r` only (`m = 0` is trivial). The cut is written out in the statement: WantedExt
may not import the OpenConjectures entry, which defines `maxCut` for its own statement. The record's
first request, to determine the largest guaranteed surplus for each `r`, is open-ended and is not
formalized here; its conjectured form (Alon, Bollobás, Krivelevich and Sudakov: `Ω(m^{3/4 + ε_r})`)
is the OpenConjectures entry `CliqueFreeMaxCutSurplusThreeQuarters`.
-/

/-- The question of Glock, Janzer and Sudakov recalled by Milojević (Oberwolfach Report 1/2026,
p. 14): there is an absolute `ε > 0` such that for every `r ≥ 3` every `K_r`-free graph `G` with `m`
edges has surplus `mc(G) - m/2 = Ω_r(m^{1/2 + ε})`, i.e. some vertex set `S` has at least
`m/2 + c_r m^{1/2 + ε}` edges to its complement (counted as the ordered pairs `(u, v)` with `u ∈ S`,
`v ∉ S` and `u v` an edge, so each crossing edge once), for a constant `c_r > 0`. -/
def absoluteEpsilonMaxCutSurplus : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℕ, 3 ≤ r → ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.CliqueFree r →
      ∃ S : Finset (Fin n),
        (G.edgeFinset.card : ℝ) / 2 + c * (G.edgeFinset.card : ℝ) ^ ((1 : ℝ) / 2 + ε) ≤
          ((Finset.univ.filter fun p : Fin n × Fin n =>
            p.1 ∈ S ∧ p.2 ∉ S ∧ G.Adj p.1 p.2).card : ℝ)

/--
Resolved true: the abstract quotes Glock, Janzer and Sudakov's "main open problem ... whether there
exists a positive absolute constant `ε` such that any `K_r`-free graph with `m` edges has surplus
`Ω_r(m^{1/2+ε})`" and presents "a result that not only resolves this problem": Theorem 1, for every
`δ > 0` there is `ε > 0` such that for every sufficiently large `m` a graph with `m` edges and no
clique of size `m^{1/2-δ}` has a cut of size at least `m/2 + m^{1/2+ε}`; small `m` are covered by
Edwards' bound `surp(G) ≥ (√(8m+1) - 1)/8`, quoted on p. 13. The resolving results are unrefereed
arXiv preprints (S. Zhang first proved surplus `c_H m^{0.5001}` for every `H`-free graph; Jin,
Milojević, Tomon and Zhang proved Theorem 1); they are used because the problem source itself
presents Theorem 1 as resolving the problem. Source: A. Milojević (with Z. Jin, I. Tomon and S.
Zhang), MaxCut in H-free graphs: recent results and connections, in Combinatorics, Oberwolfach
Reports 23 (2026), no. 1, pp. 13-14, DOI 10.4171/OWR/2026/1; resolution: Z. Jin, A. Milojević, I.
Tomon and S. Zhang, From small eigenvalues to large cuts, and Chowla's cosine problem,
arXiv:2509.03490 (2025); Z. Jin, A. Milojević and I. Tomon, Beyond the MaxCut problem in H-free
graphs, arXiv:2507.13298 (2025); S. Zhang, An Alon-Boppana-type bound for very dense graphs, with
applications to max-cut, arXiv:2507.10037 (2025); unrefereed preprints, Oberwolfach Report 1/2026,
p. 14, Theorem 1 and 'Here, we present a result that not only resolves this problem';
Jin-Milojević-Tomon-Zhang and Jin-Milojević-Tomon abstracts: every m-edge graph with no clique of
size m^{1/2-δ} has a cut of size at least m/2 + m^{1/2+ε}, ε = ε(δ) > 0; Zhang abstract: every
H-free graph with m edges has a max-cut of size at least m/2 + c_H m^{0.5001}, answering questions
of Glock-Janzer-Sudakov, https://arxiv.org/abs/2509.03490.
-/
public theorem_wanted absoluteEpsilonMaxCutSurplus_holds : absoluteEpsilonMaxCutSurplus

end MathlibExt.GraphTheory.MaxCutSurplusCliqueFreeOWR14299905Problem007Wanted
