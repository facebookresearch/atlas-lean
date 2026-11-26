# Universality of the projective hash off Diffie–Hellman pairs

Write $u = g^\alpha$, $v = g^\beta$, $w = g^\gamma$. (a) If $\gamma \ne \alpha\beta$, then for uniform $\sigma, \tau$ the pair $(h, z) = (g^\sigma u^\tau, v^\sigma w^\tau)$ is uniform on $G^2$. (b) For two pairs $(v, w), (\hat v, \hat w)$ off the Diffie–Hellman pairs and tags $\rho \ne \hat\rho$, the projections $(h_1, h_2)$ together with the two tagged hash values are uniform on $G^4$.

## Proof sketch

The exponents form an affine image of the uniform key under a matrix whose determinant is a nonzero multiple of $\gamma - \alpha\beta$ (and of $\rho - \hat\rho$ in case (b)), so the image is uniform.

## Depends on

- [Diffie–Hellman projective hash function](diffie-hellman-projective-hash.md)

## Sources

- R. Cramer and V. Shoup, "Design and Analysis of Practical Public-Key Encryption Schemes Secure against Adaptive Chosen Ciphertext Attack", SIAM Journal on Computing 33(1), 2003.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
