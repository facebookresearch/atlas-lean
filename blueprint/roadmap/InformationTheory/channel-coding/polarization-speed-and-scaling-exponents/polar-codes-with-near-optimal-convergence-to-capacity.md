# Guruswami-Riazanov-Ye: polar codes with near-optimal convergence to capacity

For every BMS channel $W$ and every $\alpha > 0$, for all sufficiently small $\delta > 0$ there are binary linear codes of block length $O(1/\delta^{2 + \alpha})$ and rate $I(W) - \delta$ that allow reliable communication over $W$ with quasi-linear time encoding and decoding. Since block length $\Omega(1/\delta^2)$ is necessary, this is a constructive version of Shannon's theorem with near-optimal dependence of block length on the gap to capacity.

## Proof sketch

Use a polar-like recursive construction with multiple carefully chosen large local kernels, one for each intermediate channel arising in successive cancellation decoding. The key ingredient is a strong converse for random linear codes on arbitrary BMS channels: above capacity even a single message bit is almost unpredictable, which shows that random kernels polarize each intermediate channel almost optimally.

## Depends on

- [Binary memoryless symmetric channels, symmetric capacity and the Bhattacharyya parameter](bhattacharyya-parameter-and-symmetric-capacity.md)

## Proof depends on

- [Fazeli-Hassani-Mondelli-Vardy: large kernels achieve the optimal scaling exponent on the erasure channel](polar-codes-with-large-kernels-achieve-optimal-scaling.md)
- [Guruswami-Xia: polar codes have polynomial gap to capacity](polynomial-gap-to-capacity-for-polar-codes.md)
- [Strong converse for discrete memoryless channels](../shannon-s-channel-coding-theorem/channel-coding-strong-converse.md)

## Sources

- Venkatesan Guruswami, Andrii Riazanov, Min Ye, "Arikan meets Shannon: polar codes with near-optimal convergence to channel capacity", STOC (2020), IEEE Transactions on Information Theory (2022); arXiv:1911.03858.
