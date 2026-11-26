# Random pairs of codes and their duals are product-expanding

For all rates $r_1, r_2 \in (0, 1)$ there is $\rho = \rho(r_1, r_2) > 0$ such that, for independent uniformly random linear codes $C_1, C_2 \subseteq \mathbb{F}_2^{\Delta}$ of dimensions $r_1 \Delta$ and $r_2 \Delta$, both $(C_1, C_2)$ and the pair of duals $(C_1^\perp, C_2^\perp)$ are $\rho$-product-expanding with probability tending to $1$ as $\Delta \to \infty$; with the same probability all four codes have linear minimum distance.

## Proof sketch

In the square case $\rho$-product-expansion is $\rho\Delta$-robustness of the pair, so this is Theorem 2.10 of Dinur, Hsieh, Lin and Vidick applied to $(C_1, C_2)$ and, since the dual of a uniformly random code of dimension $r\Delta$ is uniformly random of dimension $(1-r)\Delta$, to $(C_1^\perp, C_2^\perp)$, followed by a union bound (Corollary 2.11). The theorem itself is a Gilbert-Varshamov-style counting argument: low-weight words of $C_1 \boxplus C_2$ admitting no cheap decomposition are declared bad, organized by rank, and a union bound shows that with high probability none occurs.

## Depends on

- [Product-expansion of a pair of codes](product-expansion-of-a-pair-of-codes.md)

## Sources

- Irit Dinur, Min-Hsiu Hsieh, Ting-Chun Lin, Thomas Vidick, "Good quantum LDPC codes with linear time decoders", STOC (2023); arXiv:2206.07750, Theorem 2.10 and Corollary 2.11.
