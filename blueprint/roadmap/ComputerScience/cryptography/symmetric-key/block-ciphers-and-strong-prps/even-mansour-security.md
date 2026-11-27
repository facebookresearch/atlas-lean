# Even–Mansour is a strong PRP in the random permutation model

Model $P$ as a uniformly random permutation accessible in both directions. Every adversary making $q$ queries to the cipher (both directions) and $p$ queries to $P$ (both directions) distinguishes the Even–Mansour cipher (two keys, or a single key) from an independent random permutation with advantage at most

$$\frac{2pq}{2^n}.$$

## Proof sketch

The cipher and the independent permutation are identical until a cipher query and a direct permutation query hit the same point of $P$ after shifting by the key; since the key is uniform and hidden until such an event, each of the $pq$ pairs causes it with probability at most $2/2^n$.

## Depends on

- [Even–Mansour block cipher](even-mansour-cipher.md)
- [Strong pseudorandom permutation](strong-pseudorandom-permutation.md)

## Proof depends on

- [Fundamental lemma of game playing for stateful oracle handlers](../../security-games/identical-until-bad-oracle-handlers/fundamental-lemma-for-stateful-handlers.md)

## Sources

- S. Even and Y. Mansour, "A Construction of a Cipher from a Single Pseudorandom Permutation", Journal of Cryptology 10(3), 1997.
- O. Dunkelman, N. Keller and A. Shamir, "Minimalism in Cryptography: The Even-Mansour Scheme Revisited", Advances in Cryptology (EUROCRYPT 2012), LNCS 7237, 2012.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
