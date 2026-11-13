# Negative answer to Erdős Problem 777, second question

It is not the case that for every
real $c > 0$ there is a real constant $C$ such that for every $n$ and every family $F$ of subsets
of $\{0, \dots, n - 1\}$ with at least $c |F|^2$ comparable pairs (ordered pairs $(A, B)$ of
members of $F$ with $A \subsetneq B$), we have $|F| \le C \cdot 2^{n/2}$. Equivalently, there is
a real $c > 0$ such that for every real $C$ some $n$ and some family $F$ of subsets of
$\{0, \dots, n - 1\}$ with at least $c |F|^2$ comparable pairs have $|F| > C \cdot 2^{n/2}$.

Alon and Frankl's Example 6.1 with $d = 1$ gives such families: $m \gg n 2^{n/2}$ subsets of an
$n$-element set with at least $2^{-5} \binom{m}{2}$ comparable pairs (erdosproblems.com/777).

## Sources

- T. F. Bloom, Erdős Problems, Problem #777, https://www.erdosproblems.com/777 (status SOLVED); resolution: N. Alon and P. Frankl, The maximum number of disjoint pairs in a family of subsets, Graphs Combin. 1 (1985), 13-21; N. Alon, S. Das, R. Glebov and B. Sudakov, Comparable pairs in families of sets, J. Combin. Theory Ser. B (2015), 164-185, arXiv:1411.4196, Alon-Frankl Theorem 1.4: for every k ≥ 1 there is β(k) > 0 such that for m = 2^{(1/(k+1) + δ)n}, c(n, m) < (1 - 1/k) C(m, 2) + O(m^{2 - β δ^{k+1}}), the case k = 1 conjectured by Daykin and Erdős; Alon-Frankl Section 6, Example 6.1: the sets meeting the second half of [n] in at most d elements or missing at most d elements of the first half form a family of Θ(n^d 2^{n/2}) sets with a constant fraction of comparable pairs, disproving a conjecture of Erdős; erdosproblems.com/777: Alon and Frankl answer the third question in the affirmative and the second in the negative, and an affirmative answer to the first follows from Theorem 1.4 and Corollary 1.5 of Alon, Das, Glebov and Sudakov, https://www.erdosproblems.com/777.
