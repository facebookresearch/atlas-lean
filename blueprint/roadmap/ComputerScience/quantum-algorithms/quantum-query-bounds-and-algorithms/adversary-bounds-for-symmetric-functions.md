# Adversary lower bounds for parity, threshold functions and majority

For $N$-bit inputs and error $\varepsilon \le 1/2$, writing $\theta = 1 - 2\sqrt{\varepsilon(1-\varepsilon)}$: computing $\mathrm{PARITY}_N$ requires $\theta N \le 2T$ queries (so $N \le 36\,T$ at $\varepsilon = 1/3$), computing $\mathrm{MAJ}_N$ (for either threshold $\lceil N/2 \rceil$ or $\lfloor N/2 \rfloor + 1$) requires $\theta N \le 4T$, and distinguishing inputs of Hamming weight $a$ from inputs of weight $b$, $0 \le a < b \le N$, requires

$$\theta\,\sqrt{(N - a)\, b} \le 2T\,(b - a).$$

In particular the threshold function $\mathrm{Th}^N_k$ ($1$ iff at least $k$ ones, $1 \le k \le N$) needs $\theta\sqrt{k(N - k + 1)} \le 2T$, that is $\Omega(\sqrt{k(N - k + 1)})$ queries. At $\varepsilon = 1/3$, $\theta \ge 1/18$.

## Proof sketch

Relate inputs across single bit flips (parity, majority at the threshold), or relate each $x$ of weight $a$ with every $y \supseteq x$ of weight $b$: then $m = \binom{N-a}{b-a}$, $m' = \binom{b}{a}$, and the numbers of partners differing at a fixed index are $\binom{N-a-1}{b-a-1}$ and $\binom{b-1}{a}$; then $mm'/L = \frac{N-a}{b-a} \cdot \frac{b}{b-a}$, which gives the displayed form. For majority use the two weight layers next to the threshold.

## Depends on

- [Quantum query algorithms with phase and value oracles](../quantum-adversary-methods/quantum-query-algorithms.md)

## Proof depends on

- [Ambainis adversary bound](../quantum-query-lower-bounds/ambainis-adversary-bound.md)
- [Ambainis: relational adversary bound for non-Boolean input alphabets](../quantum-adversary-methods/ambainis-relational-adversary-for-value-queries.md)

## Sources

- A. Ambainis, "Quantum Lower Bounds by Quantum Arguments", Journal of Computer and System Sciences 64(4), 2002, Theorems 2, 5 and 6.
- A. Nayak and F. Wu, "The Quantum Query Complexity of Approximating the Median and Related Statistics", STOC 1999, Corollary 1.2 (the $\Omega$ form for weight layers).
