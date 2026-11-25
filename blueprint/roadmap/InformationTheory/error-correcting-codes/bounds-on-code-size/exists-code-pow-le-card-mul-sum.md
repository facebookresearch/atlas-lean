# Gilbert–Varshamov bound

Let $\alpha$ be a finite alphabet with $q$ letters and let $n \ge 0$ and $d \ge 1$ be natural
numbers. There is a code $C \subseteq \alpha^n$ in which any two distinct codewords are at Hamming
distance at least $d$ and

$$q^n \le |C| \sum_{i=0}^{d-1} \binom{n}{i} (q-1)^i = |C| \cdot \mathrm{Vol}_q(n, d-1).$$

The proof is Gilbert's greedy construction: a code of maximum size among the codes of minimum
distance at least $d$ is maximal, so the Hamming balls of radius $d - 1$ around its codewords
cover $\alpha^n$ ([a maximal code is covering](bi-union-ball-eq-univ-of-maximal.md)), and each
ball has $\mathrm{Vol}_q(n, d-1)$ words ([size of a Hamming ball](card-ball.md)).

Combined with the entropy bound on the volume this gives the
[rate form](exists-code-exp-le-card.md) $R \ge 1 - H_q(\delta)$; the
[linear version](exists-linear-code-finrank-eq.md) is Varshamov's.

## Informally uses

- [A maximal code is covering](bi-union-ball-eq-univ-of-maximal.md): the covering property of
  the greedy code, equation (4.2) in Guruswami, Rudra and Sudan.
- [Size of a Hamming ball](card-ball.md): the volume of each covering ball.

## Background

- [Hamming bound](hamming-sphere-packing-bound.md): the packing counterpart; balls of radius
  $\lfloor (d-1)/2 \rfloor$ are disjoint, balls of radius $d - 1$ around a maximal code cover.

## Sources

- E. N. Gilbert, "A comparison of signalling alphabets", *Bell System Technical Journal* 31 (1952), 504–522.
- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Theorem 4.2.1 and Section 4.2.1 (Algorithm 4.2.1, equation (4.2)).
