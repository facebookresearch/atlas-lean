/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Simultaneous s- and t-cores are contained in the largest one (Oberwolfach Report 15/2006)

J. B. Olsson (joint with D. Stanton, C. Bessenrodt, G. Navarro, P. H. Tiep), On block identities and
block inclusions, Oberwolfach Report 15/2006, p. 912 ff., section 2: for relatively prime positive
integers `p`, `q` there is a unique partition `κ_pq` of the maximum size `(p² - 1)(q² - 1)/24` which
is a `p`-core and a `q`-core; it is an open question whether the Young diagram of any other
partition which is a `p`-core and a `q`-core is contained in that of `κ_pq`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Young.YoungDiagram

@[expose] public section

namespace MathlibExt.Combinatorics.SimultaneousCoreContainmentOWR1265Problem006Wanted

/-!
Source: J. B. Olsson (joint with D. Stanton, C. Bessenrodt, G. Navarro, P. H. Tiep), On block
identities and block inclusions, in Representations of Finite Groups, Oberwolfach Reports 3 (2006),
no. 15, p. 912 ff., section 2 (Block identities), DOI 10.4171/OWR/2006/15. UnsolvedMath record
UM-30000448 (`OWR-1265-006`), dataset ulamai/UnsolvedMath v1.8.0.

Young diagrams are Mathlib's `YoungDiagram` (finite down-sets of `ℕ × ℕ`, containment is `≤`, size
is `card`); an `s`-core is a diagram with no hook length divisible by `s`. The report itself defines
`κ_pq` as the simultaneous core of maximum size, so the target quantifies over every simultaneous
`s`- and `t`-core `κ` of maximum size (there is one, since only finitely many simultaneous cores
exist for coprime `s`, `t`); by the report it is `κ_pq`. The hypotheses are those of the problem and
of Fayers's theorem (coprime positive integers); the cases `s = 1` or `t = 1` are included and
trivial (the only `1`-core is the empty diagram).
-/

/-- A Young diagram `μ` is an `s`-core if no cell of `μ` has hook length divisible by `s`. The hook
length of the cell `(i, j)` (row `i`, column `j`, both from `0`) is
`(μ.rowLen i - j) + (μ.colLen j - i) - 1`: the cells to its right in row `i`, the cells below it
in column `j`, and the cell itself (both differences count the cell, so one is subtracted). -/
def IsCore (s : ℕ) (μ : YoungDiagram) : Prop :=
  ∀ c ∈ μ, ¬ s ∣ (μ.rowLen c.1 - c.2) + (μ.colLen c.2 - c.1) - 1

/-- The Olsson-Stanton containment question with `κ_{s,t}` unfolded as in the report (the
partition of maximum size among those that are both an `s`-core and a `t`-core): for coprime
positive integers `s` and `t`, the Young diagram of every simultaneous `s`- and `t`-core is
contained in that of a simultaneous core of maximum size. -/
def simultaneousCoreContainment : Prop :=
  ∀ s t : ℕ, 0 < s → 0 < t → Nat.Coprime s t →
    ∀ κ : YoungDiagram, IsCore s κ → IsCore t κ →
      (∀ ν : YoungDiagram, IsCore s ν → IsCore t ν → ν.card ≤ κ.card) →
        ∀ μ : YoungDiagram, IsCore s μ → IsCore t μ → μ ≤ κ

/--
Resolved true: Fayers, Theorem 5.1 (citing Vandehey's Theorem 2.4): for coprime positive integers
`s`, `t` every `(s, t)`-core `λ` satisfies `[λ] ⊆ [κ_{s,t}]`, where `κ_{s,t}` is the `(s, t)`-core
of the largest size `(s² - 1)(t² - 1)/24`; Fayers states that this answers the question of Olsson
and Stanton. A simultaneous core `κ` of maximum size then contains every simultaneous core, since it
is itself one of them. Source: J. B. Olsson (joint with D. Stanton, C. Bessenrodt, G. Navarro, P. H.
Tiep), On block identities and block inclusions, in Representations of Finite Groups, Oberwolfach
Reports 3 (2006), no. 15, p. 912 ff., section 2 (Block identities), DOI 10.4171/OWR/2006/15;
resolution: M. Fayers, The t-core of an s-core, J. Combin. Theory Ser. A 118 (2011), 1525-1539, DOI
10.1016/j.jcta.2011.01.004, arXiv:1007.1071, Section 5, Theorem 5.1 ("Suppose s and t are coprime
positive integers, and λ is an (s, t)-core. Then [λ] ⊆ [κ_{s,t}]"), proved in Proposition 5.5;
Fayers cites the first proof as J. Vandehey, Containment in (s, t)-core partitions, arXiv:0809.2134,
Theorem 2.4, https://arxiv.org/abs/1007.1071.
-/
public theorem_wanted simultaneousCoreContainment_holds : simultaneousCoreContainment

end MathlibExt.Combinatorics.SimultaneousCoreContainmentOWR1265Problem006Wanted
