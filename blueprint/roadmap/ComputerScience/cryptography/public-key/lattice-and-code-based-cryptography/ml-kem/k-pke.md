# K-PKE, the public-key encryption scheme inside ML-KEM

K-PKE is parameterized by $n = 256$, $q = 3329$, a module rank $k$, noise widths $\eta_1, \eta_2$ and compression widths $d_u, d_v$, over $R_q = \mathbb{Z}_q[X]/(X^{256}+1)$. Key generation samples $\mathbf{A} \in R_q^{k \times k}$ (expanded from a public seed $\rho$), $\mathbf{s}, \mathbf{e} \leftarrow \mathrm{CBD}_{\eta_1}^k$, and publishes $(\rho, \mathbf{t} = \mathbf{A}\mathbf{s} + \mathbf{e})$. Encryption of $m \in \{0,1\}^{256}$ with coins $\mathbf{r} \leftarrow \mathrm{CBD}_{\eta_1}^k$, $\mathbf{e}_1 \leftarrow \mathrm{CBD}_{\eta_2}^k$, $e_2 \leftarrow \mathrm{CBD}_{\eta_2}$ outputs

$$
c = \Bigl(\mathrm{Compress}_{d_u}(\mathbf{A}^{\mathsf T}\mathbf{r} + \mathbf{e}_1),\; \mathrm{Compress}_{d_v}\bigl(\mathbf{t}^{\mathsf T}\mathbf{r} + e_2 + \mathrm{Decompress}_1(m)\bigr)\Bigr),
$$

and decryption returns $\mathrm{Compress}_1(v' - \mathbf{s}^{\mathsf T}\mathbf{u}')$ with $\mathbf{u}', v'$ the decompressed components. The noise polynomials are expanded deterministically from a seed by a pseudorandom function (SHAKE256) and the matrix by an extendable-output function (SHAKE128) with rejection sampling. The approved parameter sets are ML-KEM-512 ($k = 2$, $\eta_1 = 3$, $\eta_2 = 2$, $d_u = 10$, $d_v = 4$), ML-KEM-768 ($k = 3$, $\eta_1 = \eta_2 = 2$, $d_u = 10$, $d_v = 4$) and ML-KEM-1024 ($k = 4$, $\eta_1 = \eta_2 = 2$, $d_u = 11$, $d_v = 5$).

## Depends on

- [Ring-LWE and Module-LWE public-key encryption](../module-lattice-encryption/module-lwe-encryption.md)
- [Coefficient compression in ML-KEM](ml-kem-compression.md)
- [The centered binomial distribution](../module-lattice-encryption/centered-binomial-distribution.md)

## Sources

- National Institute of Standards and Technology, "Module-Lattice-Based Key-Encapsulation Mechanism Standard", National Institute of Standards and Technology, 2024.
- Roberto Avanzi et al., "CRYSTALS-Kyber: Algorithm Specifications and Supporting Documentation (version 3.02)", Third-round submission to the NIST post-quantum cryptography standardization process, dated 4 August 2021.
