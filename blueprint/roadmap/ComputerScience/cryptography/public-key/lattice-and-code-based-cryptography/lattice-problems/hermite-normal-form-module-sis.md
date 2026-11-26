# Module-SIS in Hermite normal form

For a module matrix $\mathbf{A} \in R_q^{d \times k}$, the systematic matrix $[\,I_d \mid \mathbf{A}\,]$, whose identity block consists of constant polynomials, acts on $(\mathbf{u}, \mathbf{z}) \in R_q^d \times R_q^k$ by $(\mathbf{u}, \mathbf{z}) \mapsto \mathbf{u} + \mathbf{A}\mathbf{z}$. Hence a short nonzero kernel vector of $[\,I \mid \mathbf{A}\,]$ is exactly a short nonzero $\mathbf{z}$ (or $\mathbf{u}$) with $\mathbf{A}\mathbf{z} \equiv -\mathbf{u}$ short. For uniform $\mathbf{A}$ this *Hermite-normal-form* Module-SIS problem is the one used in the security analysis of Dilithium and ML-DSA; since a uniform $d \times (d + k)$ matrix has an invertible left block with noticeable probability, solutions for the two forms translate into each other with the same norm bound after multiplying by that inverse.

## Proof sketch

Block multiplication gives the action; left-multiplying a uniform matrix $[\mathbf{A}_1 \mid \mathbf{A}_2]$ with $\mathbf{A}_1$ invertible by $\mathbf{A}_1^{-1}$ gives the systematic form without changing the kernel.

## Depends on

- [Module-SIS and Ring-SIS](module-sis.md)

## Sources

- Shi Bai et al., "CRYSTALS-Dilithium: Algorithm Specifications and Supporting Documentation, Version 3.1", CRYSTALS Project, 2021.
- Adeline Langlois and Damien Stehlé, "Worst-Case to Average-Case Reductions for Module Lattices", Designs, Codes and Cryptography, 2015.
