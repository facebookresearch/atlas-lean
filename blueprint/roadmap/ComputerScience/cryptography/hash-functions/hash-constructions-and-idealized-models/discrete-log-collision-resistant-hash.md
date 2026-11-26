# Collision-resistant hashing from the discrete logarithm

In a group of prime order $q$ with generator $g$ and a uniform key $h = g^{\alpha}$, the hash $H_{h}(a, b) = g^{a} h^{b}$ on $\mathbb{Z}_q^2$ is collision resistant if the discrete-logarithm problem is hard: a collision $(a, b) \ne (a', b')$ gives $\alpha = (a - a')/(b' - b)$.

## Proof sketch

From $g^a h^b = g^{a'} h^{b'}$ we get $g^{a - a'} = h^{b' - b}$; $b \ne b'$ since otherwise $a = a'$, so the discrete logarithm of $h$ is computed in $\mathbb{Z}_q$.

## Depends on

- [Discrete-logarithm experiment](../../public-key/hardness-assumptions/dlog-game.md)
- [Collision resistance and target collision resistance](../collision-resistance-and-target-collision-resistance.md)

## Proof depends on

- [Computational binding of Pedersen commitments from the discrete logarithm](../../signatures-and-protocols/commitment-schemes/pedersen-commitments-perfect-hiding-and-binding/binding-advantage-le.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- T. P. Pedersen, "Non-Interactive and Information-Theoretic Secure Verifiable Secret Sharing", Advances in Cryptology (CRYPTO 1991), LNCS 576, 1992.
