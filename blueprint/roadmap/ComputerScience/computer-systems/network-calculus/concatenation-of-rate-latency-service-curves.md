# Concatenation of rate-latency service curves

For [rate-latency functions](min-plus-algebra/rate-latency-peak-rate-affine-and-burst-delay-functions.md), $\beta_{R_1,T_1} \otimes \beta_{R_2,T_2} = \beta_{\min(R_1,R_2),\, T_1 + T_2}$. So by the [concatenation of service curves](concatenation-of-service-curves.md), a sequence of nodes offering rate-latency service curves offers the rate-latency service curve with the smallest rate and the sum of the latencies. In particular a rate-latency node $\beta_{R,T} = \delta_T \otimes \lambda_R$ behaves like a guaranteed-delay node with delay $T$ followed by a constant-rate server with rate $R$.

## Depends on

- [Rate-latency, peak-rate, affine and burst-delay functions](min-plus-algebra/rate-latency-peak-rate-affine-and-burst-delay-functions.md)
- [Concatenation of service curves](concatenation-of-service-curves.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.4.3, the examples after Theorem 1.4.6.
