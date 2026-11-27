# Intake rate and active fraction in time-constrained encounter models

An individual alternates between an **active** (searching) state and **waiting** periods. While active, it meets events of types $k = 1, \dots, n$ at independent exponential rates $\lambda_k > 0$, with $\Lambda = \sum_k \lambda_k$. An event of type $k$ brings an intake $i_k \in \mathbb R$ (negative for a cost) and is followed by a waiting time with mean $t_k \ge 0$. No events occur while waiting, and the event itself takes no time.

**Long-run intake rate.**

$$\text{intake rate} = \frac{\sum_{k=1}^{n}\lambda_k i_k}{1 + \sum_{k=1}^{n}\lambda_k t_k}.$$

**Active fraction.** The long-run fraction of time spent active, which is also the probability that a randomly observed individual is active, is

$$\rho = \frac{1}{1 + \sum_{k=1}^{n}\lambda_k t_k}.$$

For example, a territory owner that only patrols and meets intruders at rate $\lambda_i$, each fight costing time $t_w$, has $\rho_a = 1/(1 + \lambda_i t_w)$. An owner that also hunts, finding prey at rate $\lambda_h$ with handling time $t_h$, has $\rho_r = 1/(1 + \lambda_i t_w + \lambda_h t_h)$.

**Mixing over behavioural states.** Suppose an individual re-chooses between two states at rate $\lambda_r$ and after certain events, choosing state $a$ with probability $p$, and the state's cycle times are $T_a, T_r$ (the mean time from one reconsideration to the next). Then the stationary probability of being in state $a$ is

$$\pi = \frac{pT_a}{pT_a + (1-p)T_r}.$$

With the two owner states above, $\pi = p(1 + \lambda_i t_w)/(1 + \lambda_i t_w + (1-p)\lambda_h t_h)$, and the overall active fraction is $\pi\rho_a + (1-\pi)\rho_r = 1/(1 + \lambda_i t_w + (1-p)\lambda_h t_h)$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Long-run fraction of up time of an alternating renewal process](../../../../Probability/nonparametric-survival/reliability-and-monitoring/long-run-fraction-of-up-time-of-an-alternating-renewal-process.md)

## Expansion

This is the renewal–reward theorem. A cycle consists of a search, with mean $1/\Lambda$, and the waiting time after the event that ends it, with mean $\sum_k(\lambda_k/\Lambda)t_k$. The expected reward per cycle is $\sum_k(\lambda_k/\Lambda)i_k$. The long-run rate is reward per cycle over cycle length; multiplying both by $\Lambda$ gives the formula. The active fraction is the search share of the cycle, $(1/\Lambda)/(1/\Lambda + \sum_k(\lambda_k/\Lambda)t_k)$. The state probabilities follow from the same argument applied to the alternating process of behavioural states. The paper treats the population-level active proportion as equal to the individual-level time fraction, citing an earlier theorem for this class of models (large population, no synchronization).

## Sources

- T. Varga, J. Garay, J. Rychtář and M. Broom, "A temporal model of territorial defence with antagonistic interactions", *Theoretical Population Biology* (2020), <https://doi.org/10.1016/j.tpb.2020.03.005>, Section 2.2.2, Equation (2.1) and Section 2.3.5, Equations (2.2)–(2.5) and (2.8).
