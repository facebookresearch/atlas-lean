# The critical contact process dies out

Fix an integer $d \ge 1$. The contact process on $\mathbb{Z}^d$ is the Markov process on configurations $\eta \in \{0, 1\}^{\mathbb{Z}^d}$ in which an infected site ($\eta(x) = 1$) recovers at rate $1$ and a healthy site becomes infected at rate $\lambda$ times the number of its infected nearest neighbours. Write $P^{\{0\}}_\lambda$ for the law started from a single infected site at the origin. The process dies out at $\lambda$ if $P^{\{0\}}_\lambda[\eta_t = \emptyset \text{ for some } t \ge 0] = 1$, and survives otherwise; by monotonicity in $\lambda$ the critical value is $\lambda_c = \inf\{\lambda : P^{\{0\}}_\lambda[\eta_t \ne \emptyset \text{ for all } t \ge 0] > 0\}$, and $0 < \lambda_c < \infty$. Self-duality gives $\lambda_c = \lambda_c'$, where $\lambda_c' = \inf\{\lambda : \bar\nu_\lambda \ne \delta_\emptyset\}$ is defined through the upper invariant measure $\bar\nu_\lambda$, the limiting law started from all sites infected. The theorem of Bezuidenhout and Grimmett (1990), as stated by Steif and Warfheimer (2008, Theorem 1.1), is that the critical contact process dies out: at $\lambda = \lambda_c$ the process started from one infected site dies out almost surely, and hence $\bar\nu_{\lambda_c} = \delta_\emptyset$. Steif and Warfheimer (2008, Theorem 1.4) extend the result, under restrictions on the background parameter, to the contact process in a randomly evolving environment; that extension is a separate target in the Expansion.

## Proof depends on

- [Poisson process](../../../point-processes/poisson-processes/is-poisson-process.md)

## Expansion

1. The model: the graphical construction of the contact process from Poisson processes, attractiveness, and monotonicity in $\lambda$.
2. Self-duality and the equality $\lambda_c = \lambda_c'$ between survival from one site and nontriviality of the upper invariant measure.
3. The finite space–time block event of Bezuidenhout and Grimmett and the comparison with supercritical oriented percolation.
4. Conclusion: the set of $\lambda$ at which the process survives is open, so the process dies out at $\lambda_c$.
5. Separate statement: the extension to the randomly evolving environment (Steif and Warfheimer, Theorems 1.2–1.4), in which each site of $\mathbb{Z}^d$, for the same integer $d \ge 1$, carries an independent two-state background chain with parameter $p \in [0, 1]$ selecting the recovery rate $\delta_0$ or $\delta_1 \le \delta_0$, and infection rate $1$ per infected neighbour. Theorem 1.4 lowers the parameter only from a surviving $p > 0$ (survival at $p$ implies survival at $p - \varepsilon$ for some $\varepsilon > 0$), and concludes that the process dies out at $p_c$ when $p_c \in (0, 1]$; when both recovery rates are equal and small enough the ordinary supercritical contact process survives even at $p = 0$, so $p_c = 0$ and the conclusion does not apply.

## Sources

- J. E. Steif and M. Warfheimer, The critical contact process in a randomly evolving environment dies out, ALEA Lat. Am. J. Probab. Math. Stat. 4 (2008), 337–357, Section 1 (definitions, Theorems 1.1–1.4) and Section 4.
- Original result: C. Bezuidenhout and G. Grimmett, The critical contact process dies out, Ann. Probab. 18 (1990), 1462–1482. <https://doi.org/10.1214/aop/1176990627> The statement and definitions follow Steif and Warfheimer, Section 1.
