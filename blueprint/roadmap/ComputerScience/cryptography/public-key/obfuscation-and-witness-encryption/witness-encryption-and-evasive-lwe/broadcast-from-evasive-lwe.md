# Optimal broadcast encryption from evasive lattice assumptions

Assuming LWE and (a public-coin variant of) the evasive LWE assumption, there is a public-key broadcast encryption scheme for $N$ users in which the public parameters, secret keys and ciphertexts all have size $\mathrm{poly}(\lambda,\log N)$, and, more generally, a ciphertext-policy attribute-based encryption scheme for circuits with optimal parameters; security is selective. This gives broadcast encryption with parameters polylogarithmic in $N$ from lattice-type assumptions without multilinear maps or iO.

## Proof sketch

Ciphertexts are LWE samples with respect to a matrix encoding the recipient set via homomorphic attribute encodings; user keys are Gaussian preimages. Evasive LWE converts the pseudorandomness of the products available to an unauthorized coalition into pseudorandomness of the ciphertext given the preimages.

## Depends on

- [The evasive LWE assumption](evasive-lwe.md)

## Sources

- Hoeteck Wee, "Optimal Broadcast Encryption and CP-ABE from Evasive Lattice Assumptions", EUROCRYPT (2022).
