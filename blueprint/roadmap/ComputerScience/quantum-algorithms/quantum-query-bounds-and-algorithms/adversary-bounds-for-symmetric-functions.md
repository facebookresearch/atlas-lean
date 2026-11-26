# Adversary lower bounds for parity, threshold functions and majority

For $N$-bit inputs and error $\varepsilon \le 1/2$, writing $\theta = 1 - 2\sqrt{\varepsilon(1-\varepsilon)}$: computing $\mathrm{PARITY}_N$ requires $\theta N \le 2T$ queries (so $N \le 36\,T$ at $\varepsilon = 1/3$), computing $\mathrm{MAJ}_N$ requires $\theta N \le 4T$ up to rounding, and distinguishing inputs of Hamming weight $a$ from inputs of weight $b > a$ requires

$$\theta\,\sqrt{(N - a)\, b} \le 2T\,(b - a).$$

In particular $\mathrm{Th}^N_k$ needs $\Omega(\sqrt{k(N - k + 1)})$ queries.

## Proof sketch

Relate inputs across single bit flips (parity, majority at the threshold), or relate each $x$ of weight $a$ with every $y \supseteq x$ of weight $b$: then $m = \binom{N-a}{b-a}$, $m' = \binom{b}{a}$, and the numbers of partners differing at a fixed index are $\binom{N-a-1}{b-a-1}$ and $\binom{b-1}{a}$; binomial identities reduce Ambainis's bound to the displayed form.

## Depends on

- [Quantum query algorithms with phase and value oracles](../quantum-adversary-methods/quantum-query-algorithms.md)

## Proof depends on

- [Ambainis adversary bound](../quantum-query-lower-bounds/ambainis-adversary-bound.md)
- [Ambainis: relational adversary bound for non-Boolean input alphabets](../quantum-adversary-methods/ambainis-relational-adversary-for-value-queries.md)

## Sources

- A. Ambainis, "Quantum Lower Bounds by Quantum Arguments", Journal of Computer and System Sciences 64(4), 2002.
- A. Nayak and F. Wu, "The Quantum Query Complexity of Approximating the Median and Related Statistics", STOC 1999.
