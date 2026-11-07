# Inventory sequences end in short loops

Let $a_1 < \dots < a_n$ and $b_1, \dots, b_n$ be
positive integers, and iterate the inventory step starting from the pair of rows
$(a_1, \dots, a_n)$ and $(b_1, \dots, b_n)$, where the inventory step replaces a pair of rows by the
increasing list of the distinct integers occurring in either row together with the list of the
number of times each of them occurs in the two rows combined. Then there are a natural number
$t$ and a $p \in \{1, 2, 3\}$ such that the $(t + p)$-th iterate equals the $t$-th iterate.

Resolved in the affirmative: the process is the counting (inventory) map on multisets. Bronstein
and Fraenkel proved that every start is ultimately periodic, and the enumeration of all cycles
(Sauerberg and Shu, re-derived by Cain and Enin) shows that every cycle has length 1, 2 or 3.

## Sources

- V. Bronstein and A. S. Fraenkel, On a curious property of counting sequences, Amer. Math. Monthly 101 (1994), https://doi.org/10.1080/00029890.1994.11996991; J. Sauerberg and L. Shu, The long and the short on counting sequences, Amer. Math. Monthly 104 (1997), https://doi.org/10.1080/00029890.1997.11990642; O. M. Cain and S. T. Enin, Inventory loops (i.e. counting sequences) have pre-period 2 max S_1 + 60, arXiv:2004.00209 (2020), https://arxiv.org/abs/2004.00209. Moved from `OpenConjectures/Combinatorics/MultisetSequenceLoop`.
