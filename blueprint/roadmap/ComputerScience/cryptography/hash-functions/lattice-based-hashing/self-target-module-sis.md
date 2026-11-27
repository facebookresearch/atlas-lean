# The SelfTargetMSIS problem

Let $R_q = \mathbb{Z}_q[X]/(X^n + 1)$, let $\mathbf{A} \in R_q^{d \times k}$ and $\mathbf{t} \in R_q^{d}$ be uniform and independent, let $H : \{0,1\}^* \to C$ be a hash function (modelled as a random oracle) into a challenge set $C \subset R_q$ of polynomials with small coefficients, and let $\beta > 0$. The *SelfTargetMSIS* problem asks for a message $\mu$ and a vector $\mathbf{y} = (\mathbf{r}, c) \in R_q^{k+d} \times R_q$ with all coefficients in $[-\beta, \beta]$ such that

$$
H\bigl(\mu \,\Vert\, [\,I_d \mid \mathbf{A} \mid \mathbf{t}\,]\,\mathbf{y}\bigr) = c,
$$

i.e. the last coordinate of $\mathbf{y}$ equals the hash of the message and the module product it determines. Its hardness underlies the unforgeability of Dilithium and ML-DSA.

## Depends on

- [Module-SIS and Ring-SIS](../../public-key/lattice-and-code-based-cryptography/lattice-problems/module-sis.md)
- [The random oracle model](../../public-key/random-oracle-constructions/the-random-oracle-model.md)

## Sources

- Shi Bai et al., "CRYSTALS-Dilithium: Algorithm Specifications and Supporting Documentation, Version 3.1", CRYSTALS Project, 2021.
