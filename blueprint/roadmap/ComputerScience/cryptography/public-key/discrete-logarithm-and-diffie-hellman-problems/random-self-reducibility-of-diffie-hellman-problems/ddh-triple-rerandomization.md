# Rerandomization of DDH triples with a fixed first coordinate

In a group of prime order $q$ with generator $g$, fix $u = g^{\alpha}$ and map $(v, w)$ to $(v^*, w^*) = (g^{\sigma} v^{\tau},\ u^{\sigma} w^{\tau})$ for independent uniform $\sigma, \tau \in \mathbb{Z}_q$. (a) If $(u, v, w)$ is a Diffie–Hellman triple, $(u, v^*, w^*)$ is a uniform Diffie–Hellman triple with first coordinate $u$. (b) If $(u, v, w)$ is not a Diffie–Hellman triple, $(v^*, w^*)$ is uniform on $G^2$.

## Proof sketch

Writing $v = g^\beta$, $w = g^\gamma$, we get $v^* = g^{\sigma + \tau\beta}$ and $w^* = g^{\alpha\sigma + \tau\gamma}$. The linear map $(\sigma, \tau) \mapsto (\sigma + \tau\beta, \alpha\sigma + \tau\gamma)$ has determinant $\gamma - \alpha\beta$, which is nonzero exactly in case (b).

## Depends on

- [Real DDH experiment](../../elgamal-encryption/ddh-real.md)
- [Random DDH experiment](../../elgamal-encryption/ddh-rand.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. Naor and O. Reingold, "Number-Theoretic Constructions of Efficient Pseudo-Random Functions", Journal of the ACM 51(2), 2004.
