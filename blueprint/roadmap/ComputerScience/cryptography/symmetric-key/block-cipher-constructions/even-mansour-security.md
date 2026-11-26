# Security of the Even–Mansour cipher in the ideal-permutation model

For every adversary making at most $q$ queries to the cipher (in either direction) and $p$ queries to the public permutation (in either direction), the advantage in distinguishing Even–Mansour with uniform independent keys from a random permutation is at most

$$
\frac{2pq}{|G|}.
$$

Moreover: (i) for a single query, under uniform independent keys the ciphertext of any plaintext is uniform and independent of the post-whitening-free information, i.e. one cipher query is perfectly secret; (ii) the ideal game with two independent uniform permutations is equivalent to lazy bidirectional sampling of both; (iii) the variant with only pre-whitening ($k_1 = 0$) is broken by a two-query attack (one cipher query and one permutation query) that recovers $k_0$ with probability $1$.

## Proof sketch

Sample both permutations lazily; the real and ideal worlds differ only if a cipher query and a permutation query meet at a point consistent with the key, i.e. $x + k_0$ equals a queried input of $\pi$ or $y - k_1$ a queried output, which for uniform keys happens with probability at most $2pq/|G|$. For (iii), compute $\pi^{-1}(E(x))$, which equals $x + k_0$.

## Depends on

- [Even–Mansour block cipher](../block-ciphers-and-strong-prps/even-mansour-cipher.md)

## Proof depends on

- [The difference lemma](../../security-games/games-and-advantages/advantage-le-win-prob-of-eq-of-not-bad.md)

## Sources

- Shimon Even and Yishay Mansour, "A Construction of a Cipher from a Single Pseudorandom Permutation", Journal of Cryptology, 1997.
- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
- Orr Dunkelman, Nathan Keller and Adi Shamir, "Minimalism in Cryptography: The Even–Mansour Scheme Revisited", Advances in Cryptology – EUROCRYPT 2012, 2012.
