# Coefficient compression in ML-KEM

For an odd modulus $q$ (ML-KEM uses $q = 3329$) and a width $d$ with $2^d < q$, ML-KEM compresses $x \in \mathbb{Z}_q$ to $d$ bits and decompresses $y \in \mathbb{Z}_{2^d}$ by

$$
\mathrm{Compress}_d(x) = \Bigl\lfloor \tfrac{2^d}{q}\, x \Bigr\rceil \bmod 2^d, \qquad \mathrm{Decompress}_d(y) = \Bigl\lfloor \tfrac{q}{2^d}\, y \Bigr\rceil,
$$

computed on canonical representatives, where $\lfloor \cdot \rceil$ rounds to the nearest integer with ties rounded up. Both maps act coefficientwise on polynomials in $R_q$. $\mathrm{Decompress}_1$ maps the bit $0$ to $0$ and the bit $1$ to $\lfloor q/2 \rceil = (q+1)/2$, since $q$ is odd.

## Sources

- National Institute of Standards and Technology, "Module-Lattice-Based Key-Encapsulation Mechanism Standard", National Institute of Standards and Technology, 2024.
- Roberto Avanzi et al., "CRYSTALS-Kyber: Algorithm Specifications and Supporting Documentation (version 3.02)", Third-round submission to the NIST post-quantum cryptography standardization process, dated 4 August 2021.
