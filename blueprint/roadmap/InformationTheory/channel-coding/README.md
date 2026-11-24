# Channel coding

Reliable transmission over noisy channels. For a discrete memoryless channel $W$, Shannon's noisy-channel coding theorem identifies the largest rate of reliable communication with the capacity $C = \max_{P_X} I(X; Y)$: rates below $C$ are achievable with vanishing error probability, Fano's inequality gives the weak converse, and the strong converse shows that above $C$ the error probability tends to one. Gallager's
random coding bound makes achievability quantitative: averaged over random codes, the error
probability is at most $(M - 1)^\rho e^{-N E_0(\rho, p)}$, and the exponent is positive at every
rate below the mutual information.

- [Shannon's channel coding theorem](shannon-s-channel-coding-theorem/README.md)
- [Random coding bound and Gallager's exponent](random-coding-bound-and-gallager-s-exponent/README.md)
