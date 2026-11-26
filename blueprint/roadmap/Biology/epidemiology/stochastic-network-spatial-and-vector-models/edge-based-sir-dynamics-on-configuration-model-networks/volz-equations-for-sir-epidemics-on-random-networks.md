# Volz equations for SIR epidemics on random networks

**Setting.** Consider a configuration-model random network in the large-population limit with degree distribution $(p_k)_{k \ge 0}$, probability generating function $g(x) = \sum_k p_k x^k$ and finite $g'(1)$, $g''(1)$. Infection passes across each edge from an infectious to a susceptible node at rate $r > 0$, and infectious nodes recover at rate $\mu > 0$. Let $\theta(t)$ be the probability that a randomly chosen edge has not transmitted infection to its susceptible end, so that a node of degree $k$ is still susceptible with probability $\theta^k$; let $p_I(t)$ and $p_S(t)$ be the probabilities that an edge leading from a susceptible node points to an infectious, respectively susceptible, neighbour. Volz's system is

$$
\begin{aligned}
\dot\theta &= -r\,p_I\,\theta, \\
\dot p_I &= r\,p_S\,p_I\,\theta\,\frac{g''(\theta)}{g'(\theta)} - r\,p_I\,(1 - p_I) - \mu\,p_I, \\
\dot p_S &= r\,p_S\,p_I\left(1 - \theta\,\frac{g''(\theta)}{g'(\theta)}\right),
\end{aligned}
$$

with the susceptible and infectious fractions given by $S(t) = g(\theta(t))$ and $\dot I = r\,p_I\,\theta\,g'(\theta) - \mu I$.

**Proposition.**

1. $\theta$ is non-increasing, so $S(t) = g(\theta(t))$ is non-increasing, and the incidence is $-\dot S = r\,p_I\,\theta\,g'(\theta)$.
2. (Threshold) Linearizing at the disease-free state $\theta = 1$, $p_S = 1$, $p_I = 0$ gives $\dot p_I \approx (r + \mu)(R_0 - 1)\,p_I$ with

$$R_0 = \frac{r}{r + \mu}\cdot\frac{g''(1)}{g'(1)},$$

the per-edge transmissibility times the mean excess degree $\sum_k k(k-1)p_k / \sum_k k p_k$.
3. If $\theta(t) \to \theta_\infty$, the final epidemic size is $1 - g(\theta_\infty)$.
4. For a Poisson degree distribution with mean $\lambda$, $g(x) = e^{\lambda(x - 1)}$, $\theta\,g''(\theta)/g'(\theta) = \lambda\theta$, and $R_0 = \lambda\,r/(r + \mu)$; heavier-tailed degree distributions with the same mean have larger $g''(1)$ and hence larger $R_0$.

## Expansion

A degree-$k$ node remains susceptible if none of its $k$ edges has transmitted, which gives $S = \sum_k p_k \theta^k = g(\theta)$; an edge whose susceptible end has a neighbour that is infectious transmits at rate $r$, which gives $\dot\theta = -r p_I \theta$ and (1). The $g''/g'$ terms arise because the neighbour of a susceptible node reached along an edge is chosen with probability proportional to degree, and is itself still susceptible along its remaining edges; the term $-r p_I(1 - p_I)$ accounts for edges that transmit and so stop leading from a susceptible node, and $-\mu p_I$ for recovery. (2): at $\theta = 1$, $p_S = 1$ the $p_I$ equation is $\dot p_I = (r\,g''(1)/g'(1) - r - \mu)\,p_I + O(p_I^2)$. (3) is (1) in the limit, and (4) is direct computation. Degree heterogeneity therefore raises $R_0$ and accelerates early spread, while the most connected nodes are infected first, which slows the epidemic later. The reduction of the system to a single equation in $\theta$ was later given by Miller.

## Sources

- E. Volz, "SIR dynamics in random networks with heterogeneous connectivity", Journal of Mathematical Biology 56 (2008) 293–310, <https://doi.org/10.1007/s00285-007-0116-4> (PMC7080148).
- J. C. Miller, "A note on a paper by Erik Volz: SIR dynamics in random networks", Journal of Mathematical Biology 62 (2011) 349–358, <https://doi.org/10.1007/s00285-010-0337-9>.
