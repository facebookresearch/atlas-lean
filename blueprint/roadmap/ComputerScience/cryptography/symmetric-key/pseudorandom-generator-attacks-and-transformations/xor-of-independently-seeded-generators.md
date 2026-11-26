# XOR of independently seeded generators is pseudorandom if one is

Let $G_1, \dots, G_t$ be deterministic polynomial-time generators with the same output length $\ell(n)$, and with $t$ polynomial. Define $G(s_1, \dots, s_t) = G_1(s_1) \oplus \cdots \oplus G_t(s_t)$ on independent seeds. If at least one $G_j$ is a pseudorandom generator (and the index $j$ may depend on $n$), then the output of $G$ is computationally indistinguishable from uniform $\ell(n)$-bit strings. If additionally the total seed length is less than $\ell(n)$, $G$ is a pseudorandom generator.

## Proof sketch

A distinguisher for $G$ yields one for $G_j$: given a challenge $y$, sample the other seeds, XOR in their outputs and run the distinguisher. If $y$ is uniform the XOR is uniform, and if $y = G_j(s_j)$ it is distributed as the output of $G$.

## Depends on

- [Asymptotic PRG security relative to a class of distinguishers](../pseudorandom-generators/prgsecure.md)

## Sources

- T. Holenstein, "Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness", Theory of Cryptography (TCC 2006), LNCS 3876, 2006.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
