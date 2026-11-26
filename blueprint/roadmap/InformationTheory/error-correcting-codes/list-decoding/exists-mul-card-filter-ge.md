# Some ball holds many codewords

Let $C$ be a code of length $n$ over a nonempty alphabet with $q$ letters and let $e$ be a
radius. Some word $y$ satisfies

$$|C| \cdot \mathrm{Vol}_q(n, e) \le q^n \cdot |\{c \in C : \Delta(y, c) \le e\}|, \qquad \mathrm{Vol}_q(n, e) = \sum_{i=0}^{e} \binom{n}{i} (q-1)^i.$$

For a uniformly random centre $y$ each codeword lies in the ball $B(y, e)$ with probability
$\mathrm{Vol}_q(n, e)/q^n$, so the expected number of codewords in the ball is
$|C| \mathrm{Vol}_q(n, e) / q^n$ and some centre does at least as well. This is Lemma 8.1.2 of
Guruswami, Rudra and Sudan, and the averaging step (equations (7.12)–(7.16)) in their proof of the
[converse half of list-decoding capacity](exists-many-in-ball.md); with the
[volume lower bound](../bounds-on-code-size/sum-choose-mul-pow-ge-exp.md)
$\mathrm{Vol}_q(n, \rho n) \ge q^{H_q(\rho) n - o(n)}$ it forces lists of size $q^{\Omega(\varepsilon n)}$
at rate $1 - H_q(\rho) + \varepsilon$.

## Informally uses

- [Size of a Hamming ball](../bounds-on-code-size/card-ball.md): each ball around a codeword has $\mathrm{Vol}_q(n, e)$ words.

## Sources

- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Lemma 8.1.2 and the proof of Theorem 7.4.2 (ii), equations (7.12)–(7.17).
