# Weights of monotone Boolean functions and their duals (Lemma 8)

Order $\{0,1\}$ by
$0 < 1$, inputs in $\{0,1\}^n$ coordinatewise and Boolean functions on $\{0,1\}^n$ pointwise. For
such a function $f$, let $f^*(x) = \lnot f(\bar x)$ be its dual, where $\bar x$ is the
coordinatewise complement of $x$, and let $\ell(f)$ be the number of $x \in \{0,1\}^n$ with
$f(x) = 1$. Let $b$ be a monotone Boolean function on $\{0,1\}^n$. Then: if $b \le b^*$, then
$2\ell(b) \le 2^n$; if $2\ell(b) = 2^n$ and $b \le b^*$, then $b = b^*$; if $b = b^*$, then
$2\ell(b) = 2^n$; and $\ell(b^*) = 2^n - \ell(b)$. Moreover, the number of monotone Boolean
functions $f$ on $\{0,1\}^n$ with $2\ell(f) < 2^n$ equals the number of those with
$2\ell(f) > 2^n$.

For $n \ge 1$ the comparisons of $2\ell$ with $2^n$ are the paper's comparisons of $\ell$ with
$2^{n-1}$; written this way the statement also covers $n = 0$.

## Sources

- Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Lemma 8 (`jis-2025-25.6.5-lem-8`).
