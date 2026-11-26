# Joux multicollisions for iterated hash functions

Let $H$ be a Merkle–Damgård hash built from a compression function $h$ with $n$-bit chaining values. Finding $t$ successive single-block collisions $h(c_{i-1}, b_i) = h(c_{i-1}, b'_i) = c_i$ (each by a birthday search costing $O(2^{n/2})$ evaluations) yields $2^t$ distinct messages $b_1^{(\epsilon_1)} \| \cdots \| b_t^{(\epsilon_t)}$ with the same hash. Thus a $2^t$-multicollision costs $O(t \cdot 2^{n/2})$ compression evaluations. Consequently a collision for the concatenation $H_1(m) \| H_2(m)$ of two iterated hashes with $n$-bit chaining values is found with constant probability using $O(n \cdot 2^{n/2})$ compression evaluations, by evaluating $H_2$ on the messages of a $2^{n/2}$-multicollision of $H_1$.

## Proof sketch

Every choice of $\epsilon \in \{0,1\}^t$ follows the same chain of chaining values, and length padding is identical because all messages have the same length.

## Depends on

- [Merkle–Damgård hash with length strengthening](../merkle-damg-rd-construction/hash.md)

## Proof depends on

- [The birthday collision finder](birthday-collision-finder.md)

## Sources

- A. Joux, "Multicollisions in Iterated Hash Functions. Application to Cascaded Constructions", Advances in Cryptology (CRYPTO 2004), LNCS 3152, 2004.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
