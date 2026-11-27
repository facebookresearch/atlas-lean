# Secure key derivation function for a group

A (possibly keyed, with a public seed) function $H$ from group elements to $\ell$-bit strings is a *secure KDF* for a prime-order group family if $(\mathrm{seed}, H(\mathrm{seed}, g^{\gamma}))$ for uniform $\gamma$ is computationally indistinguishable from $(\mathrm{seed}, U_\ell)$. More generally, a KDF is secure for a source distribution of secrets $s$ with side information $z$ if $(z, H(s))$ is indistinguishable from $(z, U_\ell)$.

## Depends on

- [Uniform key-derivation function](../../security-of-diffie-hellman-key-exchange/is-uniform-kdf.md)

## Sources

- H. Krawczyk, "Cryptographic Extraction and Key Derivation: The HKDF Scheme", Advances in Cryptology – CRYPTO 2010, LNCS 6223, 2010, Definitions 6 and 7.
