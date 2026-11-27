# Ring-LWE and Module-LWE public-key encryption

Let $R_q = \mathbb{Z}_q[X]/(X^n+1)$, $k \ge 1$, and let $\chi_s, \chi_e$ be short secret and error laws on $R_q$. In *Module-LWE encryption* (the LPR scheme for $k = 1$), key generation draws a uniform $\mathbf{A} \in R_q^{k \times k}$ and $\mathbf{s} \leftarrow \chi_s^k$, $\mathbf{e} \leftarrow \chi_e^k$, and publishes $(\mathbf{A}, \mathbf{b} = \mathbf{A}\mathbf{s} + \mathbf{e})$; the secret key is $\mathbf{s}$. A message $m \in \{0,1\}^n$, encoded as the polynomial $\lfloor q/2 \rceil \cdot m(X)$, is encrypted with ephemeral $\mathbf{r} \leftarrow \chi_s^k$, $\mathbf{e}_1 \leftarrow \chi_e^k$, $e_2 \leftarrow \chi_e$ as

$$
(\mathbf{u}, v) = \bigl(\mathbf{A}^{\mathsf T} \mathbf{r} + \mathbf{e}_1,\; \mathbf{b}^{\mathsf T}\mathbf{r} + e_2 + \lfloor q/2 \rceil\, m\bigr).
$$

Decryption computes the phase $v - \mathbf{s}^{\mathsf T}\mathbf{u}$ and decodes each coefficient to the nearer of $0$ and $\lfloor q/2\rceil$.

## Depends on

- [Decision Module-LWE](../lattice-problems/decision-module-lwe.md)
- [The centered binomial distribution](centered-binomial-distribution.md)

## Sources

- Vadim Lyubashevsky, Chris Peikert and Oded Regev, "On Ideal Lattices and Learning with Errors over Rings", Advances in Cryptology – EUROCRYPT 2010, 2010.
- Adeline Langlois and Damien Stehlé, "Worst-Case to Average-Case Reductions for Module Lattices", Designs, Codes and Cryptography, 2015.
- Roberto Avanzi et al., "CRYSTALS-Kyber: Algorithm Specifications and Supporting Documentation (version 3.02)", Third-round submission to the NIST post-quantum cryptography standardization process, dated 4 August 2021.
