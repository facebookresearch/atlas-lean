# Accumulator in a group of unknown order

Let $(G, g)$ be a group of unknown order and $H$ a hash from elements to primes. The accumulator of a finite set $S$ is $c = g^{\prod_{x \in S} H(x)}$; adding $x \notin S$ raises $c$ to $H(x)$. A *membership proof* for $x \in S$ is $a = g^{\prod_{y \in S\setminus\{x\}} H(y)}$, checked by $a^{H(x)} = c$. A *non-membership proof* for $x \notin S$ is $(b, \gamma)$ with Bézout coefficients $\gamma E + \delta H(x) = 1$ for $E = \prod_{y\in S} H(y)$, $b = g^{\delta}$, checked by $c^{\gamma} b^{H(x)} = g$. Membership proofs for several elements aggregate by Shamir's trick.

## Depends on

- [Strong RSA assumption](strong-rsa-assumption.md)

## Sources

- J. Benaloh and M. de Mare, "One-Way Accumulators: A Decentralized Alternative to Digital Signatures", Advances in Cryptology (EUROCRYPT 1993), LNCS 765, 1994.
- J. Li, N. Li and R. Xue, "Universal Accumulators with Efficient Nonmembership Proofs", Applied Cryptography and Network Security (ACNS 2007), LNCS 4521, 2007.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
