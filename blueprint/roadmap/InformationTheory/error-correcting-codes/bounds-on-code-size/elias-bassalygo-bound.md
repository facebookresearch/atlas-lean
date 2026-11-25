# Elias–Bassalygo bound (alphabet-free form)

Let $C$ be a code of length $n$ over a nonempty alphabet with $q$ letters, with distinct codewords
at Hamming distance at least $d \le n$, and let $e \le n$ satisfy $n(n - d) < (n - e)^2$, that is
$e < n - \sqrt{n(n-d)}$. Then

$$|C| \cdot \mathrm{Vol}_q(n, e) \le n d \, q^n, \qquad \mathrm{Vol}_q(n, e) = \sum_{i=0}^{e} \binom{n}{i} (q-1)^i.$$

This is the proof of the Elias–Bassalygo bound, Theorem 8.1.1 of Guruswami, Rudra and Sudan:
[some ball of radius $e$ holds](../list-decoding/exists-mul-card-filter-ge.md) at least
$|C| \mathrm{Vol}_q(n, e)/q^n$ codewords (their Lemma 8.1.2), and by the
[Johnson bound](../list-decoding/is-list-decodable-of-johnson.md) at most $n d$. They use the
$q$-ary Johnson radius $n J_q(d/n)$ (Theorem 7.3.1) and obtain
$R \le 1 - H_q(J_q(\delta)) + o(1)$; with the alphabet-free radius used here the same argument
gives the weaker $R \le 1 - H_q(1 - \sqrt{1 - \delta}) + o(1)$, since
$J_q(\delta) \ge 1 - \sqrt{1 - \delta}$.

## Informally uses

- [Some ball holds many codewords](../list-decoding/exists-mul-card-filter-ge.md): Lemma 8.1.2, equation (8.1).
- [Every code is list decodable up to the Johnson radius](../list-decoding/is-list-decodable-of-johnson.md): equation (8.2).

## Background

- [Hamming bound](hamming-sphere-packing-bound.md): the case of radius $\lfloor (d-1)/2 \rfloor$, where the balls are disjoint and the list size is $1$.

## Sources

- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Theorem 8.1.1, Lemma 8.1.2 and its proof (equations (8.1)–(8.2)).
