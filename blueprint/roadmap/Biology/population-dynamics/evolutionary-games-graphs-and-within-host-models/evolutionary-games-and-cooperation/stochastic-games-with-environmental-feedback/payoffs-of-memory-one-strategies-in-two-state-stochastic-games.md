# Payoffs of memory-one strategies in two-state stochastic games

Two players interact for infinitely many rounds. In each round the environment is in state $s_1$ or $s_2$, and the players play a donation game in which cooperating ($C$) costs $c$ and gives the co-player a benefit $b_i$ that depends on the state, with $b_1 \ge b_2 > c$. A **transition vector** $q = (q^1_{CC}, q^1_{CD}, q^1_{DD};\ q^2_{CC}, q^2_{CD}, q^2_{DD}) \in [0,1]^6$ gives the probability $q^i_{a\tilde a}$ that the next round is in $s_1$, given the current state $s_i$ and the actions $a, \tilde a$ (symmetric: $q^i_{DC} = q^i_{CD}$). A **full-information memory-one strategy** is a vector $p = (p^i_{a\tilde a}) \in [0,1]^8$, the probability of cooperating in a round whose state is $s_i$ when the previous actions were $(a, \tilde a)$; a **no-information** strategy is one with $p^1_{a\tilde a} = p^2_{a\tilde a}$ for all $a, \tilde a$.

For strategies $p$ (player 1) and $\tilde p$ (player 2), the round outcomes $\omega = (s_i, a, \tilde a)$ form a Markov chain on $8$ states with transition probabilities

$$m_{\omega,\omega'} = x \cdot y \cdot \tilde y, \qquad x = \begin{cases} q^i_{a\tilde a} & s_{i'} = s_1 \\ 1 - q^i_{a\tilde a} & s_{i'} = s_2 \end{cases}, \quad y = \begin{cases} p^{i'}_{a\tilde a} & a' = C \\ 1 - p^{i'}_{a\tilde a} & a' = D \end{cases}, \quad \tilde y = \begin{cases} \tilde p^{i'}_{\tilde a a} & \tilde a' = C \\ 1 - \tilde p^{i'}_{\tilde a a} & \tilde a' = D \end{cases}$$

for $\omega' = (s_{i'}, a', \tilde a')$. If implementation errors make all strategy entries lie in $(0,1)$ (a strategy $p$ with error rate $\varepsilon > 0$ is played as $(1-\varepsilon)p + \varepsilon(1-p)$) and $q \ne (1,1,1;0,0,0)$, the matrix $M = (m_{\omega,\omega'})$ has a unique stationary distribution $v$, and the undiscounted long-run payoff and cooperation rate are

$$\pi(p, \tilde p) = b_1 (v^1_{CC} + v^1_{DC}) + b_2 (v^2_{CC} + v^2_{DC}) - c\,(v^1_{CC} + v^1_{CD} + v^2_{CC} + v^2_{CD}),$$

$$\gamma(p,\tilde p) = \sum_{i=1}^{2} \Big( v^i_{CC} + \tfrac12 (v^i_{CD} + v^i_{DC}) \Big).$$

With continuation probability $\delta < 1$ and first-round distribution $v_0$, the same formulas hold with the discounted occupation vector $v = (1-\delta)\, v_0 \sum_{t \ge 0} (\delta M)^t = (1-\delta)\, v_0 (I_8 - \delta M)^{-1}$.

## Proof depends on

- [Existence of a stationary distribution](../../../../../Probability/markov-chains/convergence-theorem-for-finite-markov-chains/exists-stationary.md)
- [Neumann series for the Leontief inverse when row sums are below one](../../../../../Economics/general-equilibrium/leontief-input-output-model/has-sum-pow-of-row-sum-lt-one.md)

## Proof sketch

The next state depends only on the current state and actions, and each player's next action depends only on the new state and the previous actions, independently given the past, so the joint process is a Markov chain and $m$ factorises. The one-state case $q \equiv 1$ recovers the $4$-state chain of the iterated prisoner's dilemma. With errors every action profile is reached with positive probability from every outcome; the excluded $q = (1,1,1;0,0,0)$ makes each environmental state absorbing, which splits the chain into two closed classes. The discounted formula is the normalised Neumann series of expected visit counts. Kleshnina et al. compute these quantities for all $2^8$ deterministic full-information strategies and all $2^4$ deterministic no-information strategies to compare evolution with and without information about the state; they find games where cooperation evolves only with information and others where it is most abundant without it (a benefit of ignorance).

## Sources

- M. Kleshnina, C. Hilbe, Š. Šimsa, K. Chatterjee, M. A. Nowak, "The effect of environmental information on evolution of cooperation in stochastic games", Nature Communications 14 (2023), 4153, <https://doi.org/10.1038/s41467-023-39625-9> (PMC10338504), Results (Equation 1) and Methods, "Calculation of payoffs in stochastic games", Equations 5–12.
