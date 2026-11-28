# Outbreak size and epidemic probability under bond percolation on a configuration-model network

Let a large random contact network be built by the configuration model with degree distribution $(p_k)_{k \ge 0}$, finite mean $\langle k \rangle = \sum_k k p_k$ and finite second moment $\langle k^2 \rangle$. Let

$$G_0(x) = \sum_{k} p_k x^k, \qquad G_1(x) = \frac{G_0'(x)}{G_0'(1)} = \frac{\sum_k k p_k x^{k-1}}{\langle k \rangle}$$

be the generating functions of the degree and of the excess degree (the number of further edges at the end of a uniformly chosen edge). An SIR infection is transmitted along each edge incident to an infected vertex independently with probability $T \in [0,1]$ (the transmissibility), so the final outbreak from one index case is the bond-percolation cluster containing it.

**Statements.**

1. *Reproduction number and threshold.* The mean excess degree is $\langle k_e \rangle = G_1'(1) = \langle k^2 \rangle / \langle k \rangle - 1$, and

$$R_0 = T\,\langle k_e \rangle = T\left(\frac{\langle k^2 \rangle}{\langle k \rangle} - 1\right).$$

Large epidemics are possible only above the critical transmissibility $T_c = 1/\langle k_e \rangle$, that is, when $R_0 > 1$.
2. *Mean outbreak size below threshold.* For $T < T_c$ the expected size of the outbreak started by a uniformly chosen vertex is

$$\langle s \rangle = 1 + \frac{T \langle k \rangle}{1 - T \langle k_e \rangle},$$

which diverges as $T \uparrow T_c$.
3. *Epidemic probability.* Let $u \in [0,1]$ be the smallest solution of

$$u = G_1\big(1 + (u - 1)T\big),$$

the probability that the vertex reached along a random edge does not lead to an epidemic. Then the probability that a uniformly chosen index case starts a large epidemic, which also equals the expected fraction of the population infected in that event, is

$$S = 1 - G_0\big(1 + (u - 1)T\big).$$

## Depends on

- [Epidemic percolation network for SIR epidemics](../../epidemics-on-networks/kenah-robins-epidemic-percolation-network-exact-isomorphism-of-network.md)

## Expansion

In the locally tree-like limit of the configuration model, the outbreak grows as a branching process. The index case has $k$ edges with probability $p_k$; every later case was reached along an edge and has $k-1$ further edges with probability proportional to $k p_k$. Each edge transmits with probability $T$, so the number of onward transmissions has generating function $G_1(1 - T + Tx)$ for later cases and $G_0(1 - T + Tx)$ for the index case. The mean of the first is $T G_1'(1)$, which gives $R_0$ and $T_c$. The expected total progeny of a subcritical branching process whose first generation has mean $T G_0'(1) = T\langle k\rangle$ and later generations mean $T\langle k_e\rangle$ is $1 + T\langle k\rangle \sum_{n \ge 0} (T\langle k_e\rangle)^n$, which is statement 2. The extinction probability of the edge process is the smallest fixed point of $u = G_1(1 - T + Tu)$, and the index case avoids an epidemic only if each of its edges either fails to transmit or leads to extinction, giving statement 3. In networks with very heavy-tailed degrees, $S$ can be much smaller than one even when $R_0$ is well above one, so the same $R_0$ is compatible with widely different outbreak experiences; for a Poisson degree distribution the formulas reduce to those of the fully mixed stochastic SIR model.

## Sources

- Meyers LA, Pourbohloul B, Newman ME, Skowronski DM, Brunham RC, "Network theory and SARS: predicting outbreak diversity" (2005), Section "Epidemiological analysis" (formulas for $R_0$, $\langle s\rangle$, $S$ and $u$, after Newman 2002), <https://doi.org/10.1016/j.jtbi.2004.07.026>, PMCID PMC7094100.
- M. E. J. Newman, "Spread of epidemic disease on networks", Physical Review E 66 (2002) 016128, <https://doi.org/10.1103/PhysRevE.66.016128>.
