# Decision Module-LWE

Let $R_q = \mathbb{Z}_q[X]/(X^n+1)$, let $m, d \ge 1$, and let $\chi_s$ and $\chi_e$ be distributions on $R_q^d$ and $R_q^m$ (the *secret* and *error* laws). The *real* Module-LWE game gives a distinguisher $D$ the pair $(\mathbf{A}, \mathbf{A}\mathbf{s} + \mathbf{e})$ with $\mathbf{A} \in R_q^{m \times d}$ uniform, $\mathbf{s} \leftarrow \chi_s$ and $\mathbf{e} \leftarrow \chi_e$ independent; the *random* game gives it $(\mathbf{A}, \mathbf{u})$ with $\mathbf{u}$ uniform in $R_q^m$. The advantage of $D$ is $|\Pr[D = 1 \text{ in the real game}] - \Pr[D = 1 \text{ in the random game}]|$. For a parameter family indexed by $\kappa$, the *decision Module-LWE assumption* (for the given secret and error laws) states that every probabilistic polynomial-time distinguisher has negligible advantage. Taking $n = 1$ recovers plain LWE; taking $d = 1$ gives Ring-LWE. In ML-KEM and ML-DSA the secret and error coefficients are short (centered binomial or uniform in a small interval) rather than uniform.

## Depends on

- [The negacyclic ring $\mathbb{Z}_q[X]/(X^n+1)$](negacyclic-ring.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)
- [Distinguishing advantage](../../../security-games/games-and-advantages/advantage.md)
- [Probabilistic polynomial-time Turing machines](../../../security-games/asymptotic-security/probabilistic-polynomial-time-turing-machines.md)
- [Negligible advantage](../../../security-games/asymptotic-security/negligible-adv.md)

## Sources

- Vadim Lyubashevsky, Chris Peikert and Oded Regev, "On Ideal Lattices and Learning with Errors over Rings", Advances in Cryptology – EUROCRYPT 2010, 2010.
- Adeline Langlois and Damien Stehlé, "Worst-Case to Average-Case Reductions for Module Lattices", Designs, Codes and Cryptography, 2015.
- Roberto Avanzi et al., "CRYSTALS-Kyber: Algorithm Specifications and Supporting Documentation (version 3.02)", Third-round submission to the NIST post-quantum cryptography standardization process, dated 4 August 2021.
