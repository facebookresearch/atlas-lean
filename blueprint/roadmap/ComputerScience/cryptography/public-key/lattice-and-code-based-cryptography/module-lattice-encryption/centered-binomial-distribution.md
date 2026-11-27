# The centered binomial distribution

For an integer $\eta \ge 1$, the *centered binomial distribution* $\mathrm{CBD}_\eta$ on $\mathbb{Z}$ is the law of

$$
\sum_{i=1}^{\eta} (a_i - b_i), \qquad a_1, \dots, a_\eta, b_1, \dots, b_\eta \text{ independent uniform bits}.
$$

It is supported on $[-\eta, \eta]$, symmetric, with variance $\eta/2$, and is sampled from exactly $2\eta$ fair coins. A polynomial in $R_q = \mathbb{Z}_q[X]/(X^n + 1)$ is drawn from $\mathrm{CBD}_\eta$ by sampling its $n$ coefficients independently and reducing modulo $q$; when $2\eta < q$ the centered representative of each coefficient is the sampled integer itself.

## Sources

- Roberto Avanzi et al., "CRYSTALS-Kyber: Algorithm Specifications and Supporting Documentation (version 3.02)", Third-round submission to the NIST post-quantum cryptography standardization process, dated 4 August 2021.
- National Institute of Standards and Technology, "Module-Lattice-Based Key-Encapsulation Mechanism Standard", National Institute of Standards and Technology, 2024.
