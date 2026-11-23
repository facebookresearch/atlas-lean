# Sums over merged pairs depend only on the multiset of block sizes

Let $l = (l_0, \dots, l_{r-1})$ be a list of natural numbers and $G$ a real function on finite
multisets of natural numbers. Write $[x]$ for the multiset of entries of a list $x$, and
$l^{(i,j)}$ for the list obtained from $l$ by [merging the blocks](merge-blocks.md) at positions
$i < j$. Then

$$\sum_{0 \le i < j < r} G\bigl([l^{(i,j)}]\bigr)
= \sum_{t} G\bigl(\{t_1 + t_2\} + ([l] - t)\bigr),$$

where $t = \{t_1, t_2\}$ runs over the two-element sub-multisets of $[l]$ counted with
multiplicity (one for each pair of positions $i < j$, namely $t = \{l_i, l_j\}$), $+$ adds
multisets and $[l] - t$ removes $t_1$ and $t_2$ from $[l]$ once each. The right side depends only
on $[l]$, so the left side does not change when the entries of $l$ are reordered.
