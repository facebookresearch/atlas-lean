# Simon's algorithm

Let $f : \{0,1\}^n \to \{0,1\}^n$ satisfy $f(x) = f(y)$ if and only if $y \in \{x, x \oplus s\}$, for an unknown nonzero $s \in \{0,1\}^n$. One run of the circuit $H^{\otimes n}$, query, $H^{\otimes n}$ on the first register
followed by measurement yields a uniformly random $y$ with $y \cdot s = 0 \pmod 2$. After an expected $O(n)$ runs the outcomes span the space orthogonal to $s$, and solving the resulting linear system over $\mathbb{F}_2$ determines $s$; stopping after $O(n)$ runs succeeds with probability at least $2/3$.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: Quantum query (oracle) model.

## Proof depends on

- [Inner product of bit strings modulo two](deutsch-jozsa-and-bernstein-vazirani-algorithms/bit-dot.md)

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §3.2. <https://arxiv.org/pdf/1907.09415v6>
