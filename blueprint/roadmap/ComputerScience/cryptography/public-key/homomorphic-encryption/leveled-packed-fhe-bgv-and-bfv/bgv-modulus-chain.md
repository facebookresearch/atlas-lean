# Noise management along a BGV modulus chain

Fix a chain of moduli $q_L>q_{L-1}>\dots>q_0$ with $q_j\equiv 1\pmod t$ and $q_j/q_{j-1}\approx B$, where $B$ bounds the fresh noise times $\delta_R$-factors. If a level-$j$ ciphertext has noise $\|m+te\|_\infty\le B'$ with $B'\approx B$ (a small multiple), then after tensoring and relinearization its noise is about $\delta_RB'^{2}$, and switching modulus from $q_j$ to $q_{j-1}$ (scaling by $q_{j-1}/q_j$ and rounding to the nearest ciphertext congruent modulo $t$) reduces it to about $\delta_RB'^{2}/B+t\,\delta_R\|s\|_\infty$, which is again $O(B')$ for suitable parameters. Hence each multiplicative level consumes one factor $B$ of the modulus, and evaluating a depth-$L$ circuit requires $\log q_L\approx L\log B+O(\log B)$.

## Proof sketch

Modulus switching maps $c$ to $c'=\lfloor(q_{j-1}/q_j)c\rceil$ adjusted so $c'\equiv c\pmod t$; then $c'_0+c'_1s=(q_{j-1}/q_j)(c_0+c_1s)+\tau$ with rounding error $\tau$ of norm at most $t(1+\delta_R\|s\|_\infty)$. The plaintext is preserved because $q_{j-1}\equiv q_j\equiv 1\pmod t$. Iterating, the noise after each level returns to the same magnitude, so the chain length bounds the depth.

## Depends on

- [Relinearization by gadget key switching](relinearization.md)
- [Ciphertext multiplication by tensoring](tensor-product-multiplication.md)

## Proof depends on

- [Ciphertext multiplication by tensoring](tensor-product-multiplication.md)
- [Relinearization by gadget key switching](relinearization.md)

## Sources

- Zvika Brakerski, Craig Gentry, Vinod Vaikuntanathan, "(Leveled) Fully Homomorphic Encryption without Bootstrapping", ITCS (2012), IACR ePrint 2011/277.
