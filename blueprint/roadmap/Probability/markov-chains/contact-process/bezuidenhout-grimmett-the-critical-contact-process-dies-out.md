# The critical contact process dies out

The contact process on $\mathbb{Z}^d$ is the Markov process on configurations $\eta \in \{0, 1\}^{\mathbb{Z}^d}$ in which an infected site ($\eta(x) = 1$) recovers at rate $1$ and a healthy site becomes infected at rate $\lambda$ times the number of its infected nearest neighbours. Write $P^{\{0\}}_\lambda$ for the law started from a single infected site at the origin. The process dies out at $\lambda$ if $P^{\{0\}}_\lambda[\eta_t = \emptyset \text{ for some } t \ge 0] = 1$, and survives otherwise; by monotonicity in $\lambda$ the critical value is $\lambda_c = \inf\{\lambda : P^{\{0\}}_\lambda[\eta_t \ne \emptyset \text{ for all } t \ge 0] > 0\}$, and $0 < \lambda_c < \infty$. Self-duality gives $\lambda_c = \lambda_c'$, where $\lambda_c' = \inf\{\lambda : \bar\nu_\lambda \ne \delta_\emptyset\}$ is defined through the upper invariant measure $\bar\nu_\lambda$, the limiting law started from all sites infected. The theorem of Bezuidenhout and Grimmett (1990), as stated by Steif and Warfheimer (2008, Theorem 1.1), is that the critical contact process dies out: at $\lambda = \lambda_c$ the process started from one infected site dies out almost surely, and hence $\bar\nu_{\lambda_c} = \delta_\emptyset$. Steif and Warfheimer extend the result to the contact process in a randomly evolving environment (their Theorem 1.4), whose proof shows that survival at a parameter value implies survival at a slightly smaller one, following the block construction of Bezuidenhout and Grimmett.

## Expansion

1. The model: the graphical construction of the contact process from Poisson processes, attractiveness, and monotonicity in $\lambda$.
2. Self-duality and the equality $\lambda_c = \lambda_c'$ between survival from one site and nontriviality of the upper invariant measure.
3. The finite space–time block event of Bezuidenhout and Grimmett and the comparison with supercritical oriented percolation.
4. Conclusion: the set of $\lambda$ at which the process survives is open, so the process dies out at $\lambda_c$.
5. The extension to the randomly evolving environment (Steif and Warfheimer, Theorems 1.2–1.4), as a separate statement.

## Sources

- J. E. Steif and M. Warfheimer, The critical contact process in a randomly evolving environment dies out, preprint, 2008, Section 1 (definitions, Theorem 1.1) and Section 4.
- Original result: C. Bezuidenhout and G. Grimmett, The critical contact process dies out, Ann. Probab. 18 (1990), 1462–1482. <https://doi.org/10.1214/aop/1176990627> The statement and definitions follow Steif and Warfheimer, Section 1.
