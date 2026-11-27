# SelfTargetMSIS reduces to Module-SIS in the classical random oracle model

Let $\mathcal{A}$ solve SelfTargetMSIS with probability $\varepsilon$ while making at most $Q$ queries to the random oracle $H$ with uniform challenges in a set $C$, where distinct challenges are distinct ring elements. Then there is an algorithm $\mathcal{B}$ that runs $\mathcal{A}$ twice on the same coins, answering the oracle identically up to the query that $\mathcal{A}$'s output uses and with independent fresh answers from then on, and outputs the difference of the two solutions. With probability at least

$$
\frac{\varepsilon^2}{Q} - \frac{\varepsilon}{|C|}
$$

$\mathcal{B}$ obtains, for the matrix $\mathbf{A} \in R_q^{d \times k}$, vector $\mathbf{t} \in R_q^d$ and bound $\beta$ of the SelfTargetMSIS instance, a nonzero vector $\mathbf{z}$ with $[\,I_d \mid \mathbf{A} \mid \mathbf{t}\,]\, \mathbf{z} = 0$ and coefficients bounded by $2\beta$, i.e. a Module-SIS solution for the extended matrix.

## Proof sketch

Both runs produce the same module product at the forked query, so their difference lies in the kernel; their last coordinates are distinct challenges with probability given by the general forking lemma, which makes the difference nonzero, and each coefficient at most doubles.

## Depends on

- [The SelfTargetMSIS problem](self-target-module-sis.md)
- [Module-SIS and Ring-SIS](../../public-key/lattice-and-code-based-cryptography/lattice-problems/module-sis.md)

## Proof depends on

- [The rewinding lemma](../../signatures-and-protocols/zero-knowledge-and-arguments/the-rewinding-lemma.md)
- [Module-SIS solutions are SIS solutions of the expanded matrix](../../public-key/lattice-and-code-based-cryptography/lattice-problems/module-sis-as-structured-sis.md)

## Sources

- Shi Bai et al., "CRYSTALS-Dilithium: Algorithm Specifications and Supporting Documentation, Version 3.1", CRYSTALS Project, 2021.
