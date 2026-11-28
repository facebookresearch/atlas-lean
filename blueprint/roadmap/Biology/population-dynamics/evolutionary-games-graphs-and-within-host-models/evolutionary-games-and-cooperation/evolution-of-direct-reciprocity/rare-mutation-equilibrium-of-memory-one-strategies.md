# Rare-mutation selection–mutation equilibrium of memory-one strategies

**Repeated game.** In the donation-game prisoner's dilemma with benefit $1$ and cost $0 < c < 1$ (all payoffs shifted by $c$), the payoffs to the focal player for the outcomes $CC, CD, DC, DD$ are $h_1 = (1, 0, 1 + c, c)$. A memory-one strategy is $p = (p_{CC}, p_{CD}, p_{DC}, p_{DD}) \in [0,1]^4$, the probability to cooperate after each outcome of the previous round (own move first); it is reactive if $p_{CC} = p_{DC}$ and $p_{CD} = p_{DD}$. With implementation error $\varepsilon \in (0, 1/2)$ the effective strategy is $p' = (1 - \varepsilon) p + \varepsilon (1 - p)$. Two players using $p, q$ generate a Markov chain on $\{CC, CD, DC, DD\}$ whose transition matrix has all entries positive, hence a unique stationary distribution $v$; the payoff is $\pi(p, q) = v \cdot h_1$ and the cooperation rate is $\gamma(p, q) = v_{CC} + v_{CD}$.

**Population dynamics.** In a Moran birth–death process of size $N$ with $i$ players using $p$ and $N - i$ using $q$, let $f_i, g_i$ be the fitnesses of the two types, affine in their average payoffs with selection strength $w \ge 0$. The fixation probability of a single $p$ mutant is

$$\rho(p, q) = \left(1 + \sum_{j=1}^{N-1} \prod_{i=1}^{j} \frac{g_i}{f_i}\right)^{-1},$$

which equals $1/N$ when $w = 0$. For a finite strategy set $\{p_1, \dots, p_n\}$ and vanishing mutation rate, the population is almost always homogeneous, and the sequence of resident strategies is a Markov chain with

$$m_{jk} = \frac{\rho(p_k, p_j)}{n - 1} \quad (k \ne j), \qquad m_{jj} = 1 - \sum_{k \ne j} m_{jk}.$$

For $w$ finite all off-diagonal entries are positive, so $M$ has a unique stationary distribution $\xi$ (the strategy abundances in the selection–mutation equilibrium). The long-run payoff and cooperation rate are $\bar\pi = \sum_j \xi_j \pi(p_j, p_j)$ and $\bar\gamma = \sum_j \xi_j \gamma(p_j, p_j)$.

## Proof sketch

In the birth–death process the ratio of the transition probabilities $i \to i - 1$ and $i \to i + 1$ is $g_i / f_i$, and the displayed $\rho$ is the standard absorption probability of a birth–death chain started from one mutant. When mutations are rare, each mutant fixes or goes extinct before the next arises, so only the homogeneous states matter; a mutant type is chosen uniformly among the other $n - 1$ strategies, which gives $m_{jk}$. Applied to the 16 deterministic memory-one strategies, Win-Stay Lose-Shift $(1, 0, 0, 1)$ is a self-cooperator that resists invasion when cooperation is cheap, but in a WSLS population an AllD mutant earns $1 + c$ and $c$ in alternate rounds (WSLS $(1,0,0,1)$ cooperates again after mutual defection), an average of $1/2 + c$ against the residents' mutual-cooperation payoff $1$, so WSLS loses robustness when $c > 1/2$. Among the four deterministic reactive strategies (AllD, AllC, TFT, ATFT) the dynamics cycles AllD → TFT → AllC → AllD, and AllD is the most abundant strategy. Infinite (stochastic) strategy sets are handled by discretizing $[0,1]^4$ or by the sequential-resident method that samples mutants uniformly.

## Depends on

- [Markov Matrix](../../../zero-determinant-strategies-in-iterated-games/markov-matrix.md)
- [Fixation probability in a frequency-dependent Moran process](../../../../population-genetics/moran-model/frequency-dependent-moran-fixation-product-formu.md)

## Proof depends on

- [Existence of a stationary distribution](../../../../../Probability/markov-chains/convergence-theorem-for-finite-markov-chains/exists-stationary.md)
- [Uniqueness of the stationary distribution of a primitive chain](../../../../../Probability/markov-chains/convergence-theorem-for-finite-markov-chains/stationary-unique.md)

## Sources

- S. K. Baek, H.-C. Jeong, C. Hilbe and M. A. Nowak, "Comparing reactive and memory-one strategies of direct reciprocity", *Scientific Reports* 6 (2016), 25676, section "Model and Methods" and Results on deterministic reactive and memory-one strategies, <https://doi.org/10.1038/srep25676> (PMC4861973).
