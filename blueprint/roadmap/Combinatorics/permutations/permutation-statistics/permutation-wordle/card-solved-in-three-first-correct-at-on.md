# Three-guess solves of permutations with a fixed point

Let $n \ge 4$ and let $S$ be a
permutation Wordle strategy (a permutation $S[m]$ of $\{0, \dots, m-1\}$ for each $m$) with
$S[m]$ equal to the cyclic shift $j \mapsto j + 1 \bmod m$ for every $m < n$. The number of
permutations $\pi$ of $\{0, \dots, n-1\}$ that $S$ guesses in exactly three guesses and whose
first guess (the identity) has a correct position, that is, $\pi$ has a fixed point, is
$1 - 2^{n+1} + 3^n + n^2/2 + 5n/2 - n \cdot 2^n$.

## Sources

- Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29 (2026), Article 26.1.7, Theorem 10 (`jis-2026-26.1.7-thm-10`).
