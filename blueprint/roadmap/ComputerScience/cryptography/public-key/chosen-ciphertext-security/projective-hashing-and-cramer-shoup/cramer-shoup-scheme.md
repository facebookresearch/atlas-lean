# Cramer–Shoup encryption scheme

In a prime-order group with generator $g$, the secret key is $(\alpha, \sigma, \tau, \sigma_1, \tau_1, \sigma_2, \tau_2)$, and the public key is $u = g^\alpha$, $h = g^\sigma u^\tau$, $h_1 = g^{\sigma_1}u^{\tau_1}$, $h_2 = g^{\sigma_2}u^{\tau_2}$ together with a key for a collision-resistant hash $H'$. To encrypt $m \in G$ with associated data $a$: choose $\beta$, set $v = g^\beta$, $w = u^\beta$, $e = h^\beta m$, $\rho = H'(v, w, e, a)$ and $z' = (h_1 h_2^{\rho})^\beta$; output $(v, w, e, z')$. Decryption recomputes $\rho$, rejects unless $z' = v^{\sigma_1 + \rho\sigma_2} w^{\tau_1 + \rho\tau_2}$, and outputs $e / (v^\sigma w^\tau)$.

## Depends on

- [Diffie–Hellman projective hash function](diffie-hellman-projective-hash.md)
- [Public-key encryption scheme](../../../security-games/generic-security-games/pkescheme.md)
- [Collision resistance and target collision resistance](../../../hash-functions/collision-resistance-and-target-collision-resistance.md)

## Sources

- R. Cramer and V. Shoup, "A Practical Public Key Cryptosystem Provably Secure against Adaptive Chosen Ciphertext Attack", Advances in Cryptology (CRYPTO 1998), LNCS 1462, 1998.
- R. Cramer and V. Shoup, "Design and Analysis of Practical Public-Key Encryption Schemes Secure against Adaptive Chosen Ciphertext Attack", SIAM Journal on Computing 33(1), 2003.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
