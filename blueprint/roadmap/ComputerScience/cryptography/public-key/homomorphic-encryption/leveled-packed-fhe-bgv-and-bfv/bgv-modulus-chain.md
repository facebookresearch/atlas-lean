# Noise management along a BGV modulus chain

Fix a chain of moduli $q_L>q_{L-1}>\dots>q_0$ with $q_j\equiv 1\pmod t$. Let $\mathbf{c}=(c_0,c_1)$ be a level-$j$ ciphertext with $\|[c_0+c_1s]_{q_j}\|_\infty\le E$, and let $\mathbf{c}'$ be the ciphertext closest to $(q_{j-1}/q_j)\mathbf{c}$ coefficientwise among those with $\mathbf{c}'\equiv\mathbf{c}\pmod t$ (modulus switching). If $(q_{j-1}/q_j)E+t(1+\delta_R\|s\|_\infty)<q_{j-1}/2$, then $\mathbf{c}'$ is a level-$(j-1)$ ciphertext of the same plaintext with

$$
\|[c'_0+c'_1s]_{q_{j-1}}\|_\infty\le\frac{q_{j-1}}{q_j}E+t\bigl(1+\delta_R\|s\|_\infty\bigr).
$$

Thus modulus switching divides the noise by $q_j/q_{j-1}$ up to an additive term independent of the noise; applying it after each tensoring and relinearization keeps the noise bounded relative to the current modulus, so a chain of $L+1$ moduli supports circuits of multiplicative depth $L$.

## Proof sketch

Modulus switching maps $c$ to $c'=\lfloor(q_{j-1}/q_j)c\rceil$ adjusted so $c'\equiv c\pmod t$; then $c'_0+c'_1s=(q_{j-1}/q_j)(c_0+c_1s)+\tau$ with rounding error $\tau$ of norm at most $t(1+\delta_R\|s\|_\infty)$. The plaintext is preserved because $q_{j-1}\equiv q_j\equiv 1\pmod t$. Iterating, the noise after each level returns to the same magnitude, so the chain length bounds the depth.

## Depends on

- [BGV and BFV ring ciphertexts](bgv-bfv-ciphertexts.md)

## Proof depends on

- [Relinearization by gadget key switching](relinearization.md)
- [Ciphertext multiplication by tensoring](tensor-product-multiplication.md)

## Sources

- Zvika Brakerski, Craig Gentry, Vinod Vaikuntanathan, "(Leveled) Fully Homomorphic Encryption without Bootstrapping", ITCS (2012), IACR ePrint 2011/277.
