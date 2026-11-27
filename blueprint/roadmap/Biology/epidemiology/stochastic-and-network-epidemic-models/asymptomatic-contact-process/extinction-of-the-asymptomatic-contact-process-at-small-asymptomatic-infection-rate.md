# Extinction of the asymptomatic contact process at small asymptomatic infection rate

The **asymptomatic contact process** on $\mathbb{Z}^d$ has site states $0$ (healthy), $1$ (infected, asymptomatic) and $2$ (infected, symptomatic). With $f_i(x,\xi)$ the fraction of the $2d$ nearest neighbours of $x$ in state $i$, the transitions at $x$ are

$$0 \to 1 \text{ at rate } \lambda_1 f_1(x,\xi) + \lambda_2 f_2(x,\xi), \qquad 1 \to 2 \text{ at rate } \gamma, \qquad 1 \to 0 \text{ and } 2 \to 0 \text{ at rate } 1 .$$

New infections are always asymptomatic. The process goes **extinct** if, from any initial configuration, the density of infected sites tends to $0$.

**Theorem.** For every $\gamma < 1/(4d-1)$ there is $\lambda_1(\gamma) > 0$ such that the process goes extinct whenever $\lambda_1 < \lambda_1(\gamma)$, even in the limit $\lambda_2 = \infty$.

By contrast, the mean-field model $u_1' = (\lambda_1 u_1 + \lambda_2 u_2)(1-u_1-u_2) - (\gamma+1)u_1$, $u_2' = \gamma u_1 - u_2$ has an epidemic if and only if $\lambda_1 + \gamma\lambda_2 > 1 + \gamma$, so for every $\gamma > 0$ it predicts an epidemic once $\lambda_2$ is large. The spatial model does not: local interactions cap how many times one symptomatic site can infect its neighbours.

## Depends on

- [Branching-process size of an early epidemic](../../branching-process-approximation-of-early-epidemi/bp-size.md)

## Expansion

With $\lambda_1 = 0$ and $\lambda_2 = \infty$, a symptomatic site infects each of its $2d$ neighbours at most once before recovering, and each newly infected neighbour becomes symptomatic with probability $\gamma/(\gamma+1)$. The symptomatic sites are therefore dominated by a Galton–Watson process with mean offspring below $1$ exactly when $\gamma < 1/(4d-1)$. The proof shows that the total progeny of this process has exponentially decaying tails, so infection paths have exponentially small space-time extent. A block construction then compares healthy blocks with a highly supercritical oriented percolation. Since this comparison is stable under small perturbations, extinction survives turning on a small asymptomatic infection rate $\lambda_1 > 0$.

## Sources

- Nicolas Lanchier, "On the extinction phase of the contact process with an asymptomatic state", Electronic Communications in Probability 31 (2026), 1–11, <https://doi.org/10.1214/26-ecp779>; numbering as in arXiv:2510.21092: Theorem 1 and Section 1.
