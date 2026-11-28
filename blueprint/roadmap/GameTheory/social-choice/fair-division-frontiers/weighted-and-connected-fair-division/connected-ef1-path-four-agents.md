# EF1 allocations with connected bundles on a path for up to four agents

Let the goods be the vertices of a path $g_1, g_2, \dots, g_m$, and let $n$ agents have monotone valuations on sets of goods. An allocation is connected if every bundle is a set of consecutive goods. A connected allocation is EF1 for connected bundles if for all $i, j$ there is a good $g$ at an end of the interval $X_j$ (or $X_j = \emptyset$) such that $v_i(X_i) \ge v_i(X_j \setminus \{g\})$. For $n \le 4$, a connected EF1 allocation always exists; for every $n$, a connected EF2 allocation (removing up to two end goods of the envied interval) always exists.

## Proof sketch

Discretize a moving-knife procedure. For $n \le 3$, a discrete version of Stromquist's moving knives with careful tie handling yields EF1. For $n = 4$, a combinatorial argument based on a discrete analogue of Sperner's lemma on a triangulated simplex of cut positions shows a fully labelled cell exists, giving an EF1 division. The EF2 result for all $n$ applies a discrete Sperner argument directly, where rounding each cut to a good boundary costs at most one good on each side of an envied interval.

## Depends on

- [Is EF1](../../../not-yet-classified/part-01/indivisible/is-ef1.md)

## Proof depends on

- [Cut-and-choose and Dubins-Spanier](../../cut-and-choose-and-dubins-spanier.md)
- [Cake cutting in the Robertson-Webb query model](../../cake-cutting-in-the-robertson-webb-query-model.md)

## Sources

- V. Bilò, I. Caragiannis, M. Flammini, A. Igarashi, G. Monaco, D. Peters, C. Vinci, W. S. Zwicker, "Almost Envy-Free Allocations with Connected Bundles", ITCS 2019; Games and Economic Behavior 131 (2022), arXiv:1808.09406.
