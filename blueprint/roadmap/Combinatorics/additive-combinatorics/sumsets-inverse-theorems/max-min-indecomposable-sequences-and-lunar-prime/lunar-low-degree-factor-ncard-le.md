# Decomposable lunar numbers with a low-degree factor

Let $b \ge 2$ and $n$ be natural
numbers and let $d > 0$ and $v > 0$ be reals. Count the lunar numbers $h$ of base $b$ and degree at
most $n$ that lie in $\Sigma_b^n \setminus \mathcal{H}_b^n(d)$ (decomposable but not $d$-Hoeffding
extremal) and can be written as $h = f \otimes g$, with $\otimes$ the max-min product, where $f$
and $g$ are lunar numbers of base $b$ and degree at most $n$, each with at least two nonzero
digits, and every digit $f_k$ with $k > v$ is zero. Their number is at most
$v \, n^{2d+3} \, 2^v \, (b - 1)^{(b-1)n/b + d/2}$.

The factorization is required to be nontrivial, as in the source's proof; if trivial
factorizations $h = (b - 1) \otimes h$ counted, the claim would fail at $b = 2$, $n = 2$, $d = 5$,
$v = 10^{-4}$: the lunar number with digit string $(1, 1, 1)$, that is $1 \oplus x \oplus x^2$
with $\oplus$ the lunar sum (digitwise maximum), lies in $\Sigma_2^2 \setminus \mathcal{H}_2^2(5)$,
but the bound is $8192 \cdot 10^{-4} \cdot 2^{10^{-4}} < 1$.

## Sources

- Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Lemma 27 (`jis-2025-25.2.7-lem-27`).
