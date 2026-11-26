# Modulus switching of LWE ciphertexts

For moduli $q, p \ge 1$, *modulus switching* maps a residue $x \in \mathbb{Z}_q$ to $\lfloor (p/q)\,\bar x \rceil \bmod p$, where $\bar x$ is the canonical (or centered) integer representative of $x$. Applied coefficientwise it maps a Module-LWE ciphertext $(\mathbf{u}, v)$ over $R_q$ to a ciphertext $(\mathbf{u}', v')$ over $R_p$; decryption at modulus $p$ uses the same integer secret $\mathbf{s}$ reduced modulo $p$. Switching to a smaller modulus shrinks the ciphertext and scales the noise by $p/q$, at the cost of an additive rounding error that depends on the norm of the secret.

## Depends on

- [Ring-LWE and Module-LWE public-key encryption](module-lwe-encryption.md)

## Sources

- Chris Peikert, "A Decade of Lattice Cryptography", Foundations and Trends in Theoretical Computer Science, 2016.
