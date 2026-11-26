# Bounded-noise correctness of K-PKE

For an honest K-PKE key and ciphertext, the decryption phase satisfies $v' - \mathbf{s}^{\mathsf T}\mathbf{u}' = \mathrm{Decompress}_1(m) + n_{\mathrm{dec}}$ with decryption noise

$$
n_{\mathrm{dec}} = \mathbf{e}^{\mathsf T}\mathbf{r} - \mathbf{s}^{\mathsf T}(\mathbf{e}_1 + \Delta_u) + e_2 + \Delta_v,
$$

where $\Delta_u, \Delta_v$ are the compression rounding errors of the two ciphertext components. If every coefficient of $n_{\mathrm{dec}}$ has centered absolute value at most $B$ and $4B + 2 < q$, decryption returns $m$. Uncompressed K-PKE encryption is Module-LWE encryption of the all-zero message shifted by the message polynomial $\mathrm{Decompress}_1(m)$.

## Proof sketch

Expand the decompressed ciphertext as the exact Module-LWE ciphertext plus rounding errors, cancel $\mathbf{s}^{\mathsf T}\mathbf{A}^{\mathsf T}\mathbf{r}$, and apply one-bit decoding with bounded error.

## Depends on

- [K-PKE, the public-key encryption scheme inside ML-KEM](k-pke.md)

## Proof depends on

- [Rounding properties of ML-KEM compression](ml-kem-compression-properties.md)
- [Correctness of Module-LWE encryption under bounded noise](../module-lattice-encryption/module-lwe-encryption-correctness.md)

## Sources

- National Institute of Standards and Technology, "Module-Lattice-Based Key-Encapsulation Mechanism Standard", National Institute of Standards and Technology, 2024.
- Roberto Avanzi et al., "CRYSTALS-Kyber: Algorithm Specifications and Supporting Documentation (version 3.02)", Third-round submission to the NIST post-quantum cryptography standardization process, dated 4 August 2021.
