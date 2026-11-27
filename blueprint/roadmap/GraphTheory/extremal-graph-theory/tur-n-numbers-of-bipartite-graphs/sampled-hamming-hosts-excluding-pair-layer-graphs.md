# Extremal lower bound for pair-layer graphs along Hamming sampling orders

Set $\tau=(\sqrt3-1)/2$, $\kappa=3/2-(3/4)\log_2 3$, $L=\kappa+\tau\log_2 3$ and $U=2h(\tau)-1$, with $h$ the binary entropy in bits. Define $W=\tfrac14\log_2[(97+56\sqrt3)/192]=U-L$, $\beta=(L+U)/2$ and $\gamma=3/2+W/[8(1-\beta)]$. Put $N_j=\lceil 3\cdot 2^{(1-\beta)j}\rceil$. The lower bound concerns one pair-layer graph $H$ of initial order $m\ge4$ and depth $d>0$ with $dW/2>1$, for which $\operatorname{ex}(N_j;H)\ge N_j^\gamma$ for every sufficiently large natural $j$. Neither $H$ nor the exponent varies with $j$.

## Depends on

- [Pair-layer graphs](pair-layer-graphs.md)
- [Extremal number for one forbidden graph](../extremal-number-for-one-forbidden-graph.md)

## Expansion

Decompose the source probability and entropy argument into the retained Hamming host, the exclusion of a pair-layer copy, and the lower tail for retained edges. The needed estimate is for a fixed forbidden graph along all large dimensions, with the same sampled vertex budget. Audit the entropy window and the two-sided sampling bounds before crediting the extremal conclusion.

## Sources

- [Radius fraction and certified entropy width](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L9389-L9394)
- [Entropy endpoints and midpoint](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L11457-L11462)
- [Exponent gain](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L11550-L11551)
- [Retained host estimate](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L17939-L17954)
- [Exact sampled-order inequality](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L18310-L18328)
