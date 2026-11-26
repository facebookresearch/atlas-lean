# Final size of the multi-stage pairwise SIR model

**Setting.** Pairwise SIR model on a network of $N$ nodes, each of degree $n$, with per-link transmission rate $\tau$ and an infectious period consisting of $K$ exponential stages of rate $K\gamma$ (Erlang with mean $1/\gamma$). Node and edge equations

$$\dot{[S]} = -\tau\sum_{i=1}^K [SI_i], \qquad \dot{[SS]} = -2\tau\sum_{i=1}^K [SSI_i], \qquad \dot{[SI_1]} = -(\tau + K\gamma)[SI_1] + \tau\sum_i [SSI_i] - \tau\sum_i [I_iSI_1],$$

$\dot{[SI_j]} = -(\tau + K\gamma)[SI_j] + K\gamma[SI_{j-1}] - \tau\sum_i [I_iSI_j]$ for $j \ge 2$, with the stage chain $\dot{[I_1]} = \tau\sum_i[SI_i] - K\gamma[I_1]$, $\dot{[I_j]} = K\gamma([I_{j-1}] - [I_j])$, are closed by $[XSY] \approx \frac{n-1}{n}\frac{[XS][SY]}{[S]}$.

**Theorem.** For a single outbreak in a closed population started from a vanishingly small level of infection, the final epidemic size $R_\infty = 1 - [S]_\infty/N$ satisfies

$$R_\infty = 1 - \big(1 - \tilde\tau + \tilde\tau\,\theta\big)^{n}, \qquad \theta = \big(1 - \tilde\tau + \tilde\tau\,\theta\big)^{n-1},$$

where $\tilde\tau = 1 - (K\gamma/(\tau + K\gamma))^K$ is the edge transmissibility and $\theta = S_\infty^{(n-1)/n}$. The final size depends on the infectious-period distribution only through $\tilde\tau$; since $\tilde\tau$ increases with $K$, so does $R_\infty$ at fixed mean infectious period. In the well-mixed multi-stage model the final size $R_\infty = 1 - e^{-R_0 R_\infty}$ is independent of $K$.

## Depends on

- [Edge transmissibility and epidemic threshold with Erlang infectious periods on networks](edge-transmissibility-and-threshold-with-erlang-infectious-periods.md)

## Expansion

With $a = (n-1)/n$, set $F = \sum_i [SI_i]/[S]^a$, $G = [SR]/[S]^a$, $M = [SS]/[S]^a$ and $L$ a suitable rescaling of $[SS]$; these satisfy linear equations ($\dot M = \tau M F$, $\dot G = K\gamma P_K$, …). Integrating $\dot F$ from $0$ to $\infty$, using $F(0) = F(\infty) = 0$ and the relation $G(\infty) = (\tilde\tau - 1)(L(\infty) - L(0))$, which encodes the probability that an edge to an infective ends as an $S$–$R$ edge, and $[SS]_\infty = n[S]_\infty^{2a}N^{a - 1/n}$, gives $1 - S_\infty^{1/n} = \tilde\tau\,(1 - S_\infty^{a})$. Writing $\theta = S_\infty^a$ yields the stated pair of equations. Different infectious-period distributions with the same $\tilde\tau$ give the same threshold and final size but different epidemic curves.

## Sources

- N. Sherborne, K. B. Blyuss, I. Z. Kiss, "Dynamics of multi-stage infections on networks", Bulletin of Mathematical Biology 77 (2015) 1909–1933, pairwise system (5), closure (6), Theorem 1 with equations (12)–(19) and Appendix 3; well-mixed equation (3), <https://doi.org/10.1007/s11538-015-0109-1>, PMCID: PMC4651987.
