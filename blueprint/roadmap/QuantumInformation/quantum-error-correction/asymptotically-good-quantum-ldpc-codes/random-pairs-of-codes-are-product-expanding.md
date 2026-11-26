# Random pairs of codes and their duals are product-expanding

For all rates $r_1, r_2 \in (0, 1)$ there is $\rho = \rho(r_1, r_2) > 0$ such that, for $C_1, C_2 \subseteq \mathbb{F}_2^{\Delta}$ chosen uniformly at random among codes of dimensions $\lfloor r_1 \Delta \rfloor$ and $\lfloor r_2 \Delta \rfloor$, both $(C_1, C_2)$ and $(C_1^\perp, C_2^\perp)$ are $\rho$-product-expanding with probability tending to $1$ as $\Delta \to \infty$.

## Proof sketch

A failure of product-expansion yields a low-weight matrix in $C_1 \boxplus C_2$ whose every decomposition has many nonzero rows and columns. Fixing the row and column supports, the probability that random codes contain the required patterns is exponentially small in the number of rows and columns involved, and a union bound over supports, together with a robustness argument for small supports based on the distance of random codes (Gilbert-Varshamov), gives the claim.

## Depends on

- [Product-expansion of a pair of codes](product-expansion-of-a-pair-of-codes.md)

## Sources

- Gleb Kalachev, Pavel Panteleev, "Two-sided robustly testable codes", arXiv:2206.09973 (2022).
- Irit Dinur, Min-Hsiu Hsieh, Ting-Chun Lin, Thomas Vidick, "Good quantum LDPC codes with linear time decoders", STOC (2023); arXiv:2206.07750.
