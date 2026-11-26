# Fixed-length coefficient hashing fails universality on variable-length messages

Let $F$ be any field, $\ell \ge 1$, and hash a message $(a_1, \dots, a_v)$ with $v \le \ell$ by the fixed-length evaluator $H(k, a) = a_1 k^{v-1} + \cdots + a_v$ (Horner from zero), with no length-dependent leading term. Then the empty message and the one-block message $(0)$ have equal hashes for every key $k$. Hence for every key distribution the collision probability of this pair is $1$, and the variable-length family is not $\varepsilon$-universal for any $\varepsilon < 1$.

## Proof sketch

Both messages evaluate to $0$ at every key: leading zero blocks do not change a Horner evaluation started at zero.

## Depends on

- [Collision and difference bounds for fixed-length polynomial hashing](fixed-length-polynomial-hashing.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", version 0.6, 2023.
