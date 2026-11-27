# Diffie–Hellman projective hash function

In a group of prime order $q$ with generator $g$ and public $u$, the *projective hash* with secret key $(\sigma, \tau) \in \mathbb{Z}_q^2$ has projection $h = g^{\sigma} u^{\tau}$ and maps $(v, w)$ to $z = v^{\sigma} w^{\tau}$. On a Diffie–Hellman pair ($v = g^\beta$, $w = u^\beta$) the value equals $h^\beta$, computable from the projection and $\beta$. The *tagged* (universal$_2$) variant has keys $(\sigma_1, \tau_1, \sigma_2, \tau_2)$, projections $h_i = g^{\sigma_i}u^{\tau_i}$, and maps $(v, w, \rho)$ to $v^{\sigma_1 + \rho\sigma_2} w^{\tau_1 + \rho\tau_2}$.

## Depends on

- [Real DDH experiment](../../elgamal-encryption/ddh-real.md)
- [Group exponentiation with modular exponents](../../diffie-hellman-key-exchange/gpow.md)

## Sources

- R. Cramer and V. Shoup, "Design and Analysis of Practical Public-Key Encryption Schemes Secure against Adaptive Chosen Ciphertext Attack", SIAM Journal on Computing 33(1), 2003.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
