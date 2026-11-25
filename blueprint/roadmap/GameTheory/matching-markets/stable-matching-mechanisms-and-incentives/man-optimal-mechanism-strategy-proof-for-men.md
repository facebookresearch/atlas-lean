# Strategy-proofness of the man-optimal stable mechanism for the men

Let $M$ and $W$ be finite sets of men and women, and let $h$ be a matching mechanism that returns, for every
stated profile, a man-optimal stable matching of that profile. Then truthful revelation is a dominant
strategy for every man: no man can obtain a partner he truly prefers by misreporting, whatever the others
state.

This is the men's side of Roth's Theorem 5, which Roth states for either side; the women's side follows by
exchanging the roles. Roth's footnote 4 notes that related conclusions were developed independently by
Dubins and Freedman (their paper, *Amer. Math. Monthly* 88 (1981), was not consulted for this page). Roth's
proof follows the men-proposing algorithm step by step (§5, Lemmas 1 and 2).

The hypothesis is satisfiable for markets of every size $n$ with $n$ men and $n$ women: deferred acceptance
is such a mechanism.

## Background

- [Deferred acceptance is a man-optimal stable mechanism](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/gale-shapley-algorithm/exists-is-man-optimal-stable-mechanism.md): an instance of the hypothesis for $n$ men and $n$ women.
- [Roth's impossibility theorem](not-exists-stable-strategy-proof.md): no stable mechanism is strategy-proof for both sides, so the one-sided statement is the best possible of this kind.

## Sources

- A. E. Roth, "The economics of matching: stability and incentives", *Mathematics of Operations Research* 7(4) (1982), 617–628, Theorem 5 and §5.
