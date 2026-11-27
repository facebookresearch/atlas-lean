# Naor–Reingold pseudorandom function

Let $G = \langle g\rangle$ be a group of prime order $q$. The *Naor–Reingold* function has key $(a_0, a_1, \dots, a_n) \in \mathbb{Z}_q^{n+1}$ and maps $x \in \{0,1\}^n$ to

$$F(\vec a, x) = g^{\,a_0 \prod_{i : x_i = 1} a_i}.$$

It is evaluable with $n$ multiplications in $\mathbb{Z}_q$ and one exponentiation, and the group element can be hashed to bits with a universal hash.

## Depends on

- [Group exponentiation with modular exponents](../../public-key/diffie-hellman-key-exchange/gpow.md)
- [PRF advantage](../pseudorandom-functions/prf-advantage.md)

## Sources

- M. Naor and O. Reingold, "Number-Theoretic Constructions of Efficient Pseudo-Random Functions", Journal of the ACM 51(2), 2004.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
