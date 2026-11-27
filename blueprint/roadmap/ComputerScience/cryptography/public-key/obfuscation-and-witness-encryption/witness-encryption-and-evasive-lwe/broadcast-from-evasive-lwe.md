# Optimal broadcast encryption from evasive lattice assumptions

Assuming LWE and the evasive LWE assumption for public-coin samplers ($\mathsf{aux}$ contains all of the sampler's coins), there is a selectively secure public-key broadcast encryption scheme for $N$ users in which the master public key, secret keys and ciphertexts all have size $\mathrm{poly}(\lambda,\log N)$. The same assumptions give a very selectively secure ciphertext-policy attribute-based encryption (CP-ABE) scheme for $\mathsf{NC}^1$ policies of depth $d$ and size $s$ with ciphertexts of size $\mathrm{poly}(2^{d},\log s,\lambda)$. Adding a new falsifiable \"tensor LWE\" assumption gives a very selectively secure CP-ABE scheme for circuits of a priori bounded polynomial depth $d$ and size $s$ with ciphertexts of size $\mathrm{poly}(d,\log s,\lambda)$, and master public key and secret keys of size $\ell\cdot\mathrm{poly}(d,\log s,\lambda)$ for $\ell$-bit attributes. (Both CP-ABE schemes use a strengthened form of the evasive LWE statement.) This gives broadcast encryption with parameters polylogarithmic in $N$ from lattice-type assumptions without multilinear maps or iO.

## Proof sketch

Ciphertexts are LWE samples with respect to a matrix encoding the recipient set via homomorphic attribute encodings; user keys are Gaussian preimages. Evasive LWE converts the pseudorandomness of the products available to an unauthorized coalition into pseudorandomness of the ciphertext given the preimages.

## Depends on

- [The evasive LWE assumption](evasive-lwe.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)

## Sources

- Hoeteck Wee, "Optimal Broadcast Encryption and CP-ABE from Evasive Lattice Assumptions", EUROCRYPT (2022), IACR ePrint 2023/906, Figure 1 and Sections 5.3 and 5.4.
