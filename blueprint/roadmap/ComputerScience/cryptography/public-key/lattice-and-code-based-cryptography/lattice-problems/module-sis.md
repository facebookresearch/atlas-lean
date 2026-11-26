# Module-SIS and Ring-SIS

Let $R_q = \mathbb{Z}_q[X]/(X^n + 1)$. For a module matrix $\mathbf{A} \in R_q^{d \times k}$ and a bound $\beta$, a *Module-SIS solution* is a nonzero $\mathbf{z} \in (\mathbb{Z}[X]/(X^n+1))^k$ whose coefficients all lie in $[-\beta, \beta]$ and with $\mathbf{A}\mathbf{z} \equiv 0 \pmod q$. The problem $\mathrm{MSIS}_{d,k,n,q,\beta}$ asks for such a $\mathbf{z}$ given a uniform $\mathbf{A}$; Ring-SIS is the case $d = 1$. The Module-SIS assumption for a parameter family states that every probabilistic polynomial-time solver succeeds with negligible probability. The *Hermite normal form* problem, used for signatures, asks, given a uniform $\mathbf{A}$, for a Module-SIS solution of $[\,I_d \mid \mathbf{A}\,]$: a nonzero $(\mathbf{u}, \mathbf{z}) \in (\mathbb{Z}[X]/(X^n+1))^{d} \times (\mathbb{Z}[X]/(X^n+1))^{k}$ whose coefficients all lie in $[-\beta, \beta]$ and with $\mathbf{u} + \mathbf{A}\mathbf{z} \equiv 0 \pmod q$.

## Depends on

- [The negacyclic ring $\mathbb{Z}_q[X]/(X^n+1)$](negacyclic-ring.md)
- [The short integer solution problem (SIS)](short-integer-solution-problem.md)

## Sources

- Adeline Langlois and Damien Stehlé, "Worst-Case to Average-Case Reductions for Module Lattices", Designs, Codes and Cryptography, 2015.
- Shi Bai et al., "CRYSTALS-Dilithium: Algorithm Specifications and Supporting Documentation, Version 3.1", CRYSTALS Project, 2021.
