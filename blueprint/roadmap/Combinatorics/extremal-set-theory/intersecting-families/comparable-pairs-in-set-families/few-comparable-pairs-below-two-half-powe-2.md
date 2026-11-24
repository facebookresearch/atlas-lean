# Affirmative answer to Erdős Problem 777, first question

For every real $\varepsilon > 0$
there is $N$ such that for every $n \ge N$, every family $F$ of subsets of $\{0, \dots, n - 1\}$
with $|F| \le (2 - \varepsilon) 2^{n/2}$ has fewer than $2^n$ comparable pairs, that is, ordered
pairs $(A, B)$ of members of $F$ with $A \subsetneq B$.

The bound is sharp: for even $n \ge 4$, the two stacked subcubes formed by the subsets of $\{0, \dots, n/2 - 1\}$ and the sets containing $\{0, \dots, n/2 - 1\}$ share one set, so together they form a family of $2^{n/2 + 1} - 1$ sets, with $4^{n/2} + 2 \cdot 3^{n/2} - 4 \cdot 2^{n/2} + 1 \ge 2^n$ comparable pairs. According to erdosproblems.com/777 the affirmative
answer follows from Theorem 1.4 and Corollary 1.5 of Alon, Das, Glebov and Sudakov.

## Sources

- T. F. Bloom, Erdős Problems, Problem #777, https://www.erdosproblems.com/777 (status SOLVED); resolution: Noga Alon and Péter Frankl, The maximum number of disjoint pairs in a family of subsets, Graphs Combin. 1 (1985), 13-21; Noga Alon, Shagnik Das, Roman Glebov and Benny Sudakov, Comparable pairs in families of sets, J. Combin. Theory Ser. B (2015), 164-185, arXiv:1411.4196, Alon-Frankl Theorem 1.4: for every k ≥ 1 there is β(k) > 0 such that for m = 2^{(1/(k+1) + δ)n}, c(n, m) < (1 - 1/k) C(m, 2) + O(m^{2 - β δ^{k+1}}), the case k = 1 conjectured by Daykin and Erdős; Alon-Frankl Section 6, Example 6.1: the sets meeting the second half of [n] in at most d elements or missing at most d elements of the first half form a family of Θ(n^d 2^{n/2}) sets with a constant fraction of comparable pairs, disproving a conjecture of Erdős; erdosproblems.com/777: Alon and Frankl answer the third question in the affirmative and the second in the negative, and an affirmative answer to the first follows from Theorem 1.4 and Corollary 1.5 of Alon, Das, Glebov and Sudakov, https://www.erdosproblems.com/777.
