# The occurrences of a pattern are contiguous in the suffix array

Let $s$ and $P$ be lists over a linear order of length $n$ and arbitrary length respectively. For a
row $r < n$, let $\mathrm{SA}_r$ be the entry at position $r$ of the suffix array of $s$. If
$r_1 \le r_2 \le r_3 < n$ and $P$ is a prefix of the suffixes of $s$ starting at
$\mathrm{SA}_{r_1}$ and at $\mathrm{SA}_{r_3}$, then $P$ is a prefix of the suffix of $s$
starting at $\mathrm{SA}_{r_2}$.
