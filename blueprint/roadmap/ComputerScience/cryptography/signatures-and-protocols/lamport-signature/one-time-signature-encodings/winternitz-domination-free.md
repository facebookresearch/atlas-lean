# The Winternitz checksum encoding is domination free

Write a message as $n_0$ base-$(d+1)$ digits $s_1, \dots, s_{n_0}$ and append the $n_1$ base-$(d+1)$ digits of the checksum $d\,n_0 - \sum_i s_i$, where $d\,n_0 < (d+1)^{n_1}$. The resulting encoding into $\{0, \dots, d\}^{n_0 + n_1}$ is domination free.

## Proof sketch

If the encoding of $m$ were dominated by that of $m' \ne m$, the message digits of $m$ would be at most those of $m'$ with at least one strict inequality, so the checksum of $m$ is strictly larger, which contradicts domination on the checksum digits.

## Depends on

- [Containment-free and domination-free encodings](containment-and-domination-free-encodings.md)

## Sources

- R. C. Merkle, "A Certified Digital Signature", Advances in Cryptology (CRYPTO 1989), LNCS 435, 1990.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
