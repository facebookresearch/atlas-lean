# One round of permutation Wordle

Let $S$ be a strategy, that is, a permutation $S_m$ of
$\{0, \dots, m-1\}$ for every $m$, let $\pi$ be a permutation of $\{0, \dots, n-1\}$ (the
secret), and let $g$ be a map from $\{0, \dots, n-1\}$ to itself (the current guess). Let $I$ be
the set of incorrect positions, the $k$ with $g(k) \ne \pi(k)$, and let $m$ be the number of
elements of $I$. The next guess agrees with $g$ at every position outside $I$ and permutes the
entries of $g$ on $I$ by $S_m$: writing $I = \{i_0 < i_1 < \dots < i_{m-1}\}$, it takes the value
$g(i_j)$ at $i_{S_m(j)}$ for every $j < m$.

## Sources

- Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29 (2026), Article 26.1.7, Section 2.
