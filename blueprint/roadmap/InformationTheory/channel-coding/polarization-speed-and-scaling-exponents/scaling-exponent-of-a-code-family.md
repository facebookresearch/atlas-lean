# Scaling exponent of polar codes

For a BMS channel $W$ and a fixed target block error probability $P_e \in (0, 1)$, the *scaling exponent* of a family of codes and decoders is the smallest $\mu$ such that the family achieves rate $R$ with block error at most $P_e$ at block length $N = O\big((I(W) - R)^{-\mu}\big)$ as $R \to I(W)$; equivalently, the gap to capacity at block length $N$ decays as $N^{-1/\mu}$. Random codes with optimal decoding have $\mu = 2$, which is optimal by the strong converse and second-order (dispersion) analysis.

## Depends on

- [Polar codes and successive cancellation decoding](polar-codes-and-successive-cancellation-decoding.md)
- [Strong converse for discrete memoryless channels](../shannon-s-channel-coding-theorem/channel-coding-strong-converse.md)

## Sources

- S. Hamed Hassani, Kasra Alishahi, Rudiger Urbanke, "Finite-length scaling for polar codes", IEEE Transactions on Information Theory 60(10) (2014); arXiv:1304.4778.
- Marco Mondelli, S. Hamed Hassani, Rudiger Urbanke, "Unified scaling of polar codes: error exponent, scaling exponent, moderate deviations, and error floors", IEEE Transactions on Information Theory 62(12) (2016); arXiv:1501.02444.
