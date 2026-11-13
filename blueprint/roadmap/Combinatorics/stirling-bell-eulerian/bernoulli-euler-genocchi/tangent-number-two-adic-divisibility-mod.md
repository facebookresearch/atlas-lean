# Tangent numbers: 2-adic divisibility and a congruence mod 6

Let $T \colon \mathbb{N} \to
\mathbb{Z}$ satisfy $T(0) = 0$ and, for every $m \in \mathbb{N}$,

$$T(m+1) = [m = 0] - \sum_{k=0}^{m} \binom{m}{k} T(k)\, T(m-k),$$

where $[m = 0]$ is $1$ if $m = 0$ and $0$ otherwise. Then for every $n \ge 1$, $2^n$ divides
$T(2n+1)$ and $T(2n+1)/2^n \equiv (-1)^n 4^{n-1} \pmod 6$.

These conditions determine $T$: its values are the coefficients of the exponential generating
function of $\tanh x$, the signed tangent numbers (unsigned, OEIS A009006). The source defines
the tangent numbers through $1 + \tanh x$, which agrees with this recurrence at odd indices.

## Sources

- Kwang-Wu Chen, "An Interesting Lemma for Regular C-fractions," Journal of Integer Sequences 6 (2003), Article 03.4.8, Theorem, equation, lines 362–369 (tangent numbers defined at lines 351–360), https://cs.uwaterloo.ca/journals/JIS/VOL6/Chen/chen53.tex
