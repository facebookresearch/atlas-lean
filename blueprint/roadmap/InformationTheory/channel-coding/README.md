# Channel coding

Reliable transmission over noisy channels. For a discrete memoryless channel $W$, Shannon's noisy-channel coding theorem identifies the largest rate of reliable communication with the capacity $C = \max_{P_X} I(X; Y)$: rates below $C$ are achievable with vanishing error probability, Fano's inequality gives the weak converse, and the strong converse shows that above $C$ the error probability tends to one. Gallager's
random coding bound makes achievability quantitative: averaged over random codes, the error
probability is at most $(M - 1)^\rho e^{-N E_0(\rho, p)}$, and the exponent is positive at every
rate below the mutual information.

- [Shannon's channel coding theorem](shannon-s-channel-coding-theorem/README.md)
- [Random coding bound and Gallager's exponent](random-coding-bound-and-gallager-s-exponent/README.md)

- [Capacity of the binary deletion channel](capacity-of-the-binary-deletion-channel.md)
- [Capacity region of the two-receiver broadcast channel](capacity-region-of-the-two-receiver-broadcast-channel.md)

- [Two-user discrete memoryless multiple-access channel and its capacity region](two-user-discrete-memoryless-multiple-access-channel-and-its.md)
- [Capacity of BSC, BEC and symmetric channels](capacity-of-bsc-bec-and-symmetric-channels.md)
- [Differential entropy and Gaussian maximum entropy](differential-entropy-and-gaussian-maximum-entropy.md)
- [Law of large numbers for information density](law-of-large-numbers-for-information-density.md)
- [Single-letter capacity region of the two-user multiple-access channel](remaining-clauses-of-two-user-discrete-memoryless-mac-and-ac.md)
- [Time-sharing convexity of the MAC achievable region](time-sharing-convexity-of-the-mac-achievable-region.md)
- [One-shot achievability (Shannon/Feinstein/DT bounds)](one-shot-achievability.md)
- [Polar transform: channel combining/splitting conservation](polar-transform-channel-combining-splitting-conservation.md)
