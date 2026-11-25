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

/-- **$s$-cores of Young diagrams.** Let $s$ be a natural number and $\mu$ a Young diagram, with
rows and columns numbered from $0$; write $r_i$ for the length of row $i$ of $\mu$ and $c_j$ for
the length of column $j$ of $\mu$. The hook length of the cell $(i, j)$ of $\mu$ (row $i$, column
$j$) is $(r_i - j) + (c_j - i) - 1$: the cells to its right in row $i$, the cells below it in
column $j$, and the cell itself (both differences count the cell, so one is subtracted). The
diagram $\mu$ is an *$s$-core* if no cell of $\mu$ has hook length divisible by $s$. -/
def IsCore (s : ℕ) (μ : YoungDiagram) : Prop :=
  ∀ c ∈ μ, ¬ s ∣ (μ.rowLen c.1 - c.2) + (μ.colLen c.2 - c.1) - 1

/-- **Containment of simultaneous cores (Olsson–Stanton question).** The proposition that for all
coprime positive integers $s$ and $t$ and every Young diagram $\kappa$ that is both an $s$-core and
a $t$-core and has at least as many cells as every Young diagram that is both an $s$-core and a
$t$-core, every Young diagram that is both an $s$-core and a $t$-core is contained in $\kappa$,
that is, each of its cells is a cell of $\kappa$.

The proposition does not assert that such a $\kappa$ exists. In the report, $\kappa_{s,t}$ is the
partition of maximum size that is both an $s$-core and a $t$-core, and the question is whether
the Young diagram of every such partition is contained in that of $\kappa_{s,t}$. -/
def simultaneousCoreContainment : Prop :=
  ∀ s t : ℕ, 0 < s → 0 < t → Nat.Coprime s t →
    ∀ κ : YoungDiagram, IsCore s κ → IsCore t κ →
      (∀ ν : YoungDiagram, IsCore s ν → IsCore t ν → ν.card ≤ κ.card) →
        ∀ μ : YoungDiagram, IsCore s μ → IsCore t μ → μ ≤ κ

/--
**Fayers–Vandehey containment theorem for simultaneous cores.** Call a Young diagram an
$s$-core when none of its cells has hook length divisible by $s$. For all coprime positive
integers $s$ and $t$, if $\kappa$ is a Young diagram that is both an $s$-core and a $t$-core and
has at least as many cells as every Young diagram that is both an $s$-core and a $t$-core, then
every Young diagram that is both an $s$-core and a $t$-core is contained in $\kappa$ (each of its
cells is a cell of $\kappa$).

Fayers (Theorem 5.1, first proved by Vandehey) shows that for coprime positive integers $s$ and
$t$ every simultaneous $s$- and $t$-core is contained in $\kappa_{s,t}$, the simultaneous core of
the largest size $(s^2 - 1)(t^2 - 1)/24$, answering the question of Olsson and Stanton. A
simultaneous core $\kappa$ of maximum size is then contained in $\kappa_{s,t}$ and has at least as
many cells, so it equals $\kappa_{s,t}$ and contains every simultaneous core.

Source: J. B. Olsson (joint with D. Stanton, C. Bessenrodt, G. Navarro, P. H.
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
