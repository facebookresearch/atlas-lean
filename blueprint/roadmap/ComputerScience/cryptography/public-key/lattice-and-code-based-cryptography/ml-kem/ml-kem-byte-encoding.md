# ML-KEM byte encoding and seed-expansion conventions

FIPS 203 encodes a polynomial with $d$-bit coefficients ($1 \le d \le 12$) by $\mathrm{ByteEncode}_d$ as $32d$ bytes, little-endian bitwise; $\mathrm{ByteDecode}_d \circ \mathrm{ByteEncode}_d$ is the identity for $d < 12$, and for $d = 12$ decoding reduces each 12-bit value modulo $q = 3329$, so $\mathrm{ByteEncode}_{12}$ is injective on $\mathbb{Z}_q^{256}$. Seed expansion uses two domain-separated interfaces: matrix entry $(i, j)$ is sampled by SampleNTT from SHAKE128 absorbing $\rho \Vert j \Vert i$ (column byte before row byte), parsing three bytes into two 12-bit candidates and rejecting those $\ge q$; noise is sampled by $\mathrm{SamplePolyCBD}_\eta$ from SHAKE256 absorbing a seed and one counter byte. Longer XOF requests extend shorter ones, the noise widths $\eta = 2, 3$ absorb identical bytes (width $2$ returns the first $128$ bytes of width $3$), and within each of K-PKE.KeyGen and K-PKE.Encrypt the counter byte takes distinct values (both algorithms start it at $0$, under the different seeds $\sigma$ and $r$), so every noise polynomial of an algorithm reads its own PRF output.

## Proof sketch

Bit-level encoding and decoding are inverse on values below $2^d$; for $d = 12$ every canonical residue is below $2^{12}$.

## Depends on

- [K-PKE, the public-key encryption scheme inside ML-KEM](k-pke.md)

## Sources

- National Institute of Standards and Technology, "Module-Lattice-Based Key-Encapsulation Mechanism Standard", National Institute of Standards and Technology, 2024.
- Roberto Avanzi et al., "CRYSTALS-Kyber: Algorithm Specifications and Supporting Documentation (version 3.02)", Third-round submission to the NIST post-quantum cryptography standardization process, dated 4 August 2021.
