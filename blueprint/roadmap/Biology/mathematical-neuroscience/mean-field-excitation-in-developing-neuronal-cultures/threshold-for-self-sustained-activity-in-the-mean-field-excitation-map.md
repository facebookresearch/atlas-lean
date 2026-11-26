# Threshold for self-sustained activity in the mean-field excitation map

Consider a connected network of neurons in which each neuron has on average $z > 0$ neighbours, and a neuron fires at the next time step with probability $p \in (0,1)$ in response to each excited neighbour, independently. If $q_t \in [0,1]$ is the fraction of excited neurons at time $t$, the mean-field dynamics is

$$q_{t+1} = 1 - (1-p)^{z q_t}.$$

**Proposition.** The interval $[0,1]$ is forward invariant, every forward orbit $(q_t)$ is monotone in $t$, and the only attractors are fixed points. Moreover:

1. if $-z\log(1-p) \le 1$, the only fixed point is $q_1^* = 0$, and it attracts every orbit;
2. if $-z\log(1-p) > 1$, there are exactly two fixed points: $q_1^* = 0$ is a repeller and $q_2^* \in (0,1)$ is a stable attractor.

Hence the transition to self-sustained activity occurs at the critical connectivity

$$\bar z_1 = \frac{-1}{\log(1-p)}, \qquad p = \frac{1}{\bar z_1} + O\!\left(\frac{1}{\bar z_1^2}\right),$$

and the nonzero steady level $q_2^*$ satisfies $(1 - q_2^*)^{1/q_2^*} = (1-p)^z$, increasing with $z$.

## Expansion

The map $f(q) = 1 - e^{zq\log(1-p)}$ is increasing and strictly concave on $[0,1]$, with $f(0) = 0$, $f(1) < 1$ and $f'(0) = -z\log(1-p)$. An increasing one-dimensional map has monotone orbits converging to fixed points. Concavity allows at most one positive fixed point, which exists exactly when the slope at the origin exceeds $1$, in which case the origin is repelling and the positive fixed point attracting. This mirrors the percolation picture of the geometric model, in which a spanning cluster of connected cells appears once the mean number of neighbours exceeds a critical value.

## Sources

- I. Y. Tyukin, D. Iudin, F. Iudin, T. Tyukina, V. Kazantsev, I. Mukhina and A. N. Gorban, "Simple model of complex dynamics of activity patterns in developing networks of neuronal cultures", *PLOS ONE* 14 (2019), e0218304, section "Mean-field dynamic model of neuronal excitation", Eqs. (2)–(3) and Proposition 1, proved in the Appendix. <https://doi.org/10.1371/journal.pone.0218304> (PMC6597067)
