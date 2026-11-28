# Rare-mutation limit of the pairwise comparison process

Let a population of $N \ge 2$ players use strategies from a finite set $P$, with a symmetric two-player payoff function $\pi(p, \tilde p)$ (the payoff to $p$ against $\tilde p$) and a cooperation rate $\gamma(p, \tilde p) \in [0,1]$. In a population of $k$ mutants with strategy $p_M$ and $N - k$ residents with $p_R$, each player meets every other player once, so the average payoffs are

$$\pi_R(k) = \frac{N-k-1}{N-1}\,\pi(p_R,p_R) + \frac{k}{N-1}\,\pi(p_R,p_M), \qquad \pi_M(k) = \frac{N-k}{N-1}\,\pi(p_M,p_R) + \frac{k-1}{N-1}\,\pi(p_M,p_M).$$

In the **pairwise comparison process** with selection strength $\beta \ge 0$, a randomly chosen learner adopts the strategy of a randomly chosen role model with probability given by the Fermi function $(1 + e^{-\beta(\pi_{\text{model}} - \pi_{\text{learner}})})^{-1}$. The probability that a single mutant takes over a resident population is

$$\rho(p_R, p_M) = \frac{1}{1 + \sum_{i=1}^{N-1} \prod_{k=1}^{i} \exp\!\big(-\beta\,(\pi_M(k) - \pi_R(k))\big)},$$

which equals $1/N$ at $\beta = 0$. If mutations are so rare that each mutant fixes or is lost before the next arises, and a mutant adopts a strategy drawn uniformly from $P$, the sequence of resident strategies is a Markov chain on $P$ with transition probabilities $\rho(p, \tilde p)/|P|$ for $\tilde p \ne p$. For $\beta < \infty$ this chain is irreducible, its stationary distribution $w = (w_p)_{p \in P}$ is unique, and the long-run average payoff and cooperation rate of the population are

$$\hat\pi = \sum_{p \in P} w_p\, \pi(p,p), \qquad \hat\gamma = \sum_{p \in P} w_p\, \gamma(p,p).$$

## Proof depends on

- [Fixation probability in a frequency-dependent Moran process](../../../../population-genetics/moran-model/frequency-dependent-moran-fixation-product-formu.md)
- [Existence of a stationary distribution](../../../../../Probability/markov-chains/convergence-theorem-for-finite-markov-chains/exists-stationary.md)
- [Uniqueness of the stationary distribution of a primitive chain](../../../../../Probability/markov-chains/convergence-theorem-for-finite-markov-chains/stationary-unique.md)
- [Strong law for finite irreducible Markov chains, including periodic chains](../../../../../Probability/markov-chains/convergence-theorem-for-finite-markov-chains/strong-law-for-additive-functionals-of-finite-ir.md)

## Proof sketch

The number of mutants is a birth–death chain absorbing at $0$ and $N$: it moves up when a resident learner copies a mutant model and down in the reverse case, with probabilities equal to a common combinatorial factor (the chance of drawing a mutant–resident learner–model pair) times the corresponding Fermi factor. The ratio of down to up probabilities is $\gamma_k = e^{-\beta(\pi_M(k) - \pi_R(k))}$, because the two Fermi factors differ by exactly that ratio; the general birth–death fixation formula then gives $\rho$. Self-interactions are excluded, which is why the resident meets $N-k-1$ residents and the mutant $k-1$ mutants. Every fixation probability is positive for finite $\beta$, so the embedded chain is irreducible and the time averages of $\pi(p_t,p_t)$ and $\gamma(p_t,p_t)$ along the resident sequence converge to their stationary expectations, independently of the initial resident. Kleshnina et al. use this process with the stochastic-game payoffs of memory-one strategies and define the value of information about the environment as $V_\beta(q) = \hat\gamma_F - \hat\gamma_N$, the difference in cooperation between full-information and no-information strategy sets; they analyse it analytically for weak selection ($\beta \to 0$) and numerically for arbitrary $\beta$.

## Sources

- M. Kleshnina, C. Hilbe, Š. Šimsa, K. Chatterjee, M. A. Nowak, "The effect of environmental information on evolution of cooperation in stochastic games", Nature Communications 14 (2023), 4153, <https://doi.org/10.1038/s41467-023-39625-9> (PMC10338504), Methods, "Evolutionary dynamics", Equations 13–19.
- A. Traulsen, M. A. Nowak, J. M. Pacheco, "Stochastic dynamics of invasion and fixation", Physical Review E 74 (2006), 011909, <https://doi.org/10.1103/PhysRevE.74.011909>.
