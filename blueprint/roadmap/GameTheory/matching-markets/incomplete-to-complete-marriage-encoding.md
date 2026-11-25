# Incomplete-to-complete marriage encoding

This node collects the encoding of marriage markets with incomplete preference lists into complete markets.

Let a marriage market have finite sets of men and women, possibly of different sizes, in which each agent strictly ranks the agents of
the other side that it finds acceptable, acceptability is mutual, and remaining single ranks below every acceptable partner and above
every unacceptable one, as for [stable matchings with singles](rural-hospitals-theorem/is-stable-single.md). Let $S$ be the set of agents
matched in some stable matching; by the rural hospitals theorem ([men](rural-hospitals-theorem/rural-hospitals-same-men.md),
[women](rural-hospitals-theorem/rural-hospitals-same-women.md)) every stable matching matches exactly the agents of $S$, so $S$ contains
as many men as women. The completed market $J$ has the agents of $S$, and each agent's list consists of its acceptable partners in $S$,
in its own order, followed by the other agents of the opposite side in $S$ in a fixed arbitrary order. Then:

1. every stable matching with singles of the original market, restricted to $S$, is a stable perfect matching of $J$: a pair blocking it
   in $J$ is acceptable, since unacceptable partners are ranked below every partner the matching assigns, and would block it in the
   original market;
2. every stable perfect matching $\mu$ of $J$ uses only acceptable pairs: take a stable matching $\mu_0$ of the original market, stable in
   $J$ by 1; $\mu$ matches the men who prefer $\mu_0$ to $\mu$ with women who prefer $\mu$ to $\mu_0$, while an unacceptable pair of $\mu$
   would be a man who prefers $\mu_0$ matched with a woman who also prefers $\mu_0$;
3. the converse of 1 fails, because agents outside $S$ can still block. With men $m_1, m_2$, women $w_1, w_2, w_3$, every pair acceptable,
   $m_1 : w_1 \succ w_2 \succ w_3$, $m_2 : w_3 \succ w_1 \succ w_2$, $w_1 : m_2 \succ m_1$, $w_2 : m_2 \succ m_1$ and
   $w_3 : m_1 \succ m_2$, the only stable matching is $\{m_1 w_1, m_2 w_3\}$, so $S$ omits $w_2$; the matching $\{m_1 w_3, m_2 w_1\}$ is
   stable in $J$, but $(m_1, w_2)$ blocks it in the original market.

Scott (2005, §§1.3.1–1.3.2) describes this deletion-and-completion construction and states that the two sets of stable matchings
coincide; item 3 shows that only the inclusion of item 1 holds.

## Expansion

A sound expansion has separate pages for:

1. **Restriction.** Items 1 and 2 above, with the matching of men who prefer one stable matching to women who prefer the other as a
   proof prerequisite.
2. **Exact encoding.** A complete market with equal sides, built by keeping every agent and adding dummy agents, whose stable perfect
   matchings correspond exactly to the stable matchings with singles of the original market, with the positions of the unacceptable
   partners and the dummies in every list, and with the preservation of individual rationality, blocking pairs, the set of single
   agents, and men- and women-optimality. The sources cited here do not state one.
3. **Comparison** with the [bridge to the stable marriage model](rural-hospitals-theorem/stable-with-singles-iff-stable-perfect-matching.md),
   which treats only equal sides with every partner acceptable; the new statements must not restate it.

No unconditional bijection between stable matchings with singles and stable perfect matchings of a complete market is asserted.

## Depends on

- [Stable matching with singles](rural-hospitals-theorem/is-stable-single.md)
- [Rural hospitals theorem, marriage case: every stable matching matches the same men](rural-hospitals-theorem/rural-hospitals-same-men.md)
- [Rural hospitals theorem, marriage case: every stable matching matches the same women](rural-hospitals-theorem/rural-hospitals-same-women.md)
- [Stable perfect matching](../../GraphTheory/matchings-and-flows/stable-marriage-problem/is-stable.md)
- [Blocking pair](../../GraphTheory/matchings-and-flows/stable-marriage-problem/is-blocking-pair.md)

## Related topics

- [Bridge to the stable marriage model](rural-hospitals-theorem/stable-with-singles-iff-stable-perfect-matching.md)
- [The Gale-Shapley matching](../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/gale-shapley-algorithm/gs-matching.md)

## Sources

- S. Scott, *A Study of Stable Marriage Problems with Ties*, PhD thesis, University of Glasgow, 2005, §1.3.1 (unequal sides: the same agents are matched in every stable matching, after Gale and Sotomayor 1985) and §1.3.2 (incomplete lists and the deletion-and-completion construction). <https://www.dcs.gla.ac.uk/~davidm/pubs/SandyScottThesis.pdf>
- D. Gale and L. S. Shapley, *College Admissions and the Stability of Marriage*, Amer. Math. Monthly 69 (1962), 9–15, §2 (applicants omit the colleges they would never accept) and §4 (deferred acceptance with such lists). <https://www.math.utoronto.ca/~mccann/assignments/477/GaleShapley62.pdf>
