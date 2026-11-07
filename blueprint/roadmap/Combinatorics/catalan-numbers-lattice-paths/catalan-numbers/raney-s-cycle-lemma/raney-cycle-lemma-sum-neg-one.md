# Raney's cycle lemma

Let $a = (a_0, \dots, a_{n-1})$ be a list of integers, each at least
$-1$, whose entries sum to $-1$. Then there is exactly one index $r$ with $0 \le r < n$ such that
every proper prefix of the rotation $(a_r, \dots, a_{n-1}, a_0, \dots, a_{r-1})$ has nonnegative
sum: for every $t$ with $0 \le t < n$, the sum of the first $t$ entries of this rotation is at
least $0$.

The hypothesis that every entry is at least $-1$ is not needed; Raney's cycle lemma for arbitrary
integer lists proves the same conclusion without it.

## Sources

- <https://cs.uwaterloo.ca/journals/JIS/VOL24/Haupt/haupt4.tex>, lines 804-807. Lean's zero-based left rotation is a bijective reindexing of the source's cut after `a_r`; `t < a.length` ranges over every proper prefix, with `t = 0` giving the true empty-prefix condition. The lower bound `hlower` is not needed; see `raney_cycle_lemma_sum_neg_one_general`.
