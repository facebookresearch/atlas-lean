# Permuting the entries of a map along a set of positions

Let $I$ be a subset of
$\{0, \dots, n-1\}$ with $k$ elements, listed in increasing order as
$i_0 < i_1 < \dots < i_{k-1}$, let $\sigma$ be a permutation of $\{0, \dots, k-1\}$, and let $g$
be a map from $\{0, \dots, n-1\}$ to itself. Applying $\sigma$ to $g$ along $I$ gives the map that
takes the value $g(i_j)$ at $i_{\sigma(j)}$ for every $j < k$ and agrees with $g$ outside $I$.

## Sources

- Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29 (2026), Article 26.1.7, Section 2 (the action of a strategy component on `𝓘_r`).
