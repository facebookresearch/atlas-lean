# Inserting a digit and the digit sum

Let $n \ge 1$ have the $\ell$ decimal digits
$d_{\ell-1} \dots d_1 d_0$, so that $n = \sum_{j\lt \ell} d_j 10^j$. Let $S(n)$ be the set of the
numbers $\sum_{j\lt i} d_j 10^j + x \cdot 10^i + \sum_{i \le j < \ell} d_j 10^{j+1}$ with
$0 \le i \le \ell$ and $x \in \{0, \dots, 9\}$, excluding $i = \ell$ with $x = 0$: these are the
numbers obtained by inserting one decimal digit $x$ anywhere in the decimal expansion of $n$,
without creating a leading zero. Then the number of elements of $S(n)$ that are at most $10n$,
that is, the position of $10n$ when $S(n)$ is listed in increasing order, equals the digit sum
$d_0 + d_1 + \dots + d_{\ell-1}$ of $n$ (A007953).

## Sources

- Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29 (2026), Article 26.1.8, Theorem 6 (`jis-2026-26.1.8-thm-6`).
