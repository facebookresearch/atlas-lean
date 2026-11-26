# Regret bound for sparse-sampling corticostriatal learning

**Task.** In a static $A$-alternative forced-choice task ($A$-armed Bernoulli bandit), choosing action $a$ yields reward $r \in \{0,1\}$ with probability $\mu_a$; the regret after $T$ trials is the expected total reward of always choosing the best action minus that of the algorithm, $\sum_{t=1}^{T}(\mu_{a^*} - \mu_{a_t})$ in expectation.

**Algorithm (basic CogLink).** Action $a$ is represented by $M$ corticostriatal weights $v_{t,a,1}, \dots, v_{t,a,M}$, initialized to $\bar V_{a,m}$. At trial $t$:
1. for each $a$, sparse premotor activity selects a uniformly random $K$-subset $\{i_1 < \dots < i_K\} \subseteq \{1,\dots,M\}$ and forms the sample $\hat v_{t,a} = \frac1K\sum_{j=1}^{K} v_{t,a,i_j}$ (so the value belief $V_{t,a}$ is the uniform distribution over $K$-subset averages);
2. the motor stage picks $a_t = \arg\max_a \hat v_{t,a}$ (winner-take-all) and reward $r_t$ is received;
3. each weight of the chosen ensemble is updated by its own (distributional) reward prediction error, $v_{t+1,a_t,m} = v_{t,a_t,m} + \eta(N_{t,a_t})\,(r_t - v_{t,a_t,m})$, where $N_{t,a}$ counts previous choices of $a$; other ensembles are unchanged.

**Theorem.** If the sparsity $K$, the learning rates $\eta$ and the initial weights $\bar V_{a,m}$ are chosen appropriately, the regret after $T$ trials is at most

$$C\sqrt{A\,T\,\log(AT)}$$

for a constant $C$. In the formal version, $K = 1$, $\eta(n) = 1/(1+n)$ and the initial weights are $\bar V_{a,m} = c\,m/M$, with $c$ an explicit logarithmic factor in $A$, $T$ and the reward gaps, divided by the gap between the best and second-best action; the constant then depends on the ratio of reward gaps. Since every algorithm suffers regret of order $\sqrt{AT}$ in the worst case, the circuit is minimax-optimal up to a logarithmic factor.

## Expansion

With $K = 1$ and $\eta(n) = 1/(1+n)$, after $n$ choices of $a$ each weight equals $(\bar V_{a,m} + r_1 + \dots + r_n)/(n+1)$: the empirical mean reward shrunk toward an optimistic offset $c\,m/M$ whose influence decays like $1/(n+1)$. Sampling a uniformly random neuron therefore adds a random optimism bonus of size up to $c/(n+1)$ to the empirical mean, which plays the role of the posterior spread in Thompson sampling: rarely chosen actions keep wide value beliefs and are explored, frequently chosen ones concentrate and are exploited. The regret analysis bounds the number of times a suboptimal action can win the sampled comparison in terms of the bonus scale and concentration of the empirical means. Larger $K$ averages more weights and narrows the belief, shifting the balance toward exploitation.

## Sources

- M. B. Wang, N. Lynch, M. M. Halassa, "The neural basis for uncertainty processing in hierarchical decision making", Nature Communications (2025), Results Eqs. (2.6)–(2.8) and Theorem 1, Methods (algorithm pseudo-code, Eq. (4.15) and Theorem 2 with proof), <https://doi.org/10.1038/s41467-025-63994-y>, PMCID PMC12531367.
