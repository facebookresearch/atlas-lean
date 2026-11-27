# Three outputs of the Java linear congruential generator determine its seed

Take $q = 2^{48}$, $a = \mathtt{0x5DEECE66D}$, $b = 11$ and $w = 2^{22}$, so that each output $\lfloor s_i / w \rfloor$ reveals the top 26 bits of the state. For every seed $s < 2^{48}$, exhaustive search over the $2^{22}$ candidates $r_1 w + e$ ($0 \le e < w$) for the first state, keeping one whose next two outputs agree with $r_2$ and $r_3$, returns $s$. Hence three consecutive outputs determine the seed and all subsequent outputs, by a search of $2^{22}$ steps.

## Proof sketch

The candidate set contains the true state. Uniqueness is a finite check: for each of the $2^{26}$ values of $r_1$ the map from the $2^{22}$ low parts to the pair of next outputs is injective for these parameters, which is verified by the structure of the multiplier modulo $2^{48}$.

## Depends on

- [Linear congruential generator](linear-congruential-generator.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
