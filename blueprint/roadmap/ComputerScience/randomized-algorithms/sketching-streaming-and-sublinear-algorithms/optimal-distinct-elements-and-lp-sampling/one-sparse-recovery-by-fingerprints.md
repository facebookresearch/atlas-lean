# Exact 1-sparse recovery and detection with three linear counters

For a turnstile stream over $[n]$ whose coordinates stay in $\{-M, \dots, M\}$, let $Q = \max\{n^2, nM + 1\}$, let $q$ be a prime with $Q < q \le 2Q$ (one exists by Bertrand's postulate), and let $z$ be uniform in $\mathbb{F}_q$. Maintain the three linear counters

$$
a = \sum_{i} x_i, \qquad b = \sum_{i} i\, x_i, \qquad f = \sum_{i} x_i z^{i} \bmod q .
$$

Here $a$ and $b$ are exact integers. If $x$ has exactly one nonzero coordinate $x_j$, then $a \ne 0$, $b/a = j$, $x_j = a$ and $f = a z^{j} \bmod q$. If $x$ has at least two nonzero coordinates, then the test "$a \ne 0$, $b/a \in [n]$ and $f = a z^{b/a} \bmod q$" passes with probability at most $n/q < 1/n$ over $z$. Since $q \le 2Q$, $|a| \le nM$ and $|b| \le n^2 M$, 1-sparse recovery with detection uses $O(\log q + \log(nM)) = O(\log n)$ bits when $M = \mathrm{poly}(n)$. Running it on random subsets of coordinates yields $s$-sparse recovery with $O(s \log(s/\delta))$ instances of $O(\log n)$ bits, so $O(s \log n \log(s/\delta))$ bits, which fails with probability at most $\delta$ plus the false-positive probability of the fingerprint tests, at most $n/q$ for each of the $O(s\log(s/\delta))$ tests.

## Proof sketch

The first claim is direct substitution. In the second case the polynomial $g(Z) = \sum_i x_i Z^{i} - a Z^{b/a}$ over $\mathbb{F}_q$ is nonzero, since $x$ has two nonzero coordinates and $q > nM \ge |x_i|$ for every $i$, so at least one coefficient $x_i$ with $i \ne b/a$ survives modulo $q$, and it has degree at most $n$, so it has at most $n$ roots and $\Pr_z[g(z) = 0] \le n/q$. For $s$-sparse recovery, hash the coordinates into $O(s)$ buckets with a pairwise independent hash function so that each support element is alone in its bucket with constant probability, run the 1-sparse test in every bucket and repeat $O(\log(s/\delta))$ times.

## Depends on

- [Turnstile streams, support size and linear sketches of a frequency vector](turnstile-streams-and-support-size.md)

## Proof depends on

- [Pairwise-independent hashing by affine maps over GF(2)](../../../../TheoryOfComputation/counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)
- [Universal hash family](../../../data-structures/hashing/universal-hashing/is-universal.md)
- [A polynomial over an integral domain has at most as many roots as its degree](../../../../Algebra/zeros-of-polynomials/card-roots-le-degree.md)

## Sources

- Hossein Jowhari, Mert Sağlam, Gábor Tardos, "Tight Bounds for Lp Samplers, Finding Duplicates in Streams, and Related Problems", PODS (2011), arXiv:1012.4889.
- Kook Jin Ahn, Sudipto Guha, Andrew McGregor, "Analyzing Graph Structure via Linear Measurements", SODA (2012).
