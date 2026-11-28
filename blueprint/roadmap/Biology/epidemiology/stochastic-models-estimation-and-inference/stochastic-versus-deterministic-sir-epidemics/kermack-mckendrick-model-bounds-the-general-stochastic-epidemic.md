# The Kermack–McKendrick model bounds the general stochastic epidemic

**Setting.** In the general stochastic SIR epidemic on a finite population $\mathcal{V}$, $|\mathcal{V}| = N$, every infected individual makes infectious contacts with each other individual according to independent Poisson processes of rate $\beta$ and recovers after an exponential time of rate $\gamma$. Start from a non-random state with initial susceptibles $\mathcal{S}_0$ and initial infectives $\mathcal{I}_0 = \mathcal{V}\setminus\mathcal{S}_0$, $|\mathcal{S}_0|, |\mathcal{I}_0| \ge 1$, and let $X(t)$, $Y(t)$, $Z(t)$ be the numbers susceptible, infected and recovered. The deterministic Kermack–McKendrick system with matched parameters is

$$\dot S = -\beta S I, \qquad \dot I = \beta S I - \gamma I, \qquad \dot R = \gamma I, \qquad S(0) = |\mathcal{S}_0|,\ I(0) = |\mathcal{I}_0|,\ R(0) = 0.$$

**Theorem.** For the same initial conditions and parameters,
1. $\mathbb{E}[X(t)] > S(t)$ for all $t > 0$;
2. $\mathbb{E}[Z(t)] < R(t)$ for all $t > 0$;
3. if $T = \inf\{t > 0 : Y(t) = 0\}$ is the duration of the stochastic epidemic, then $\mathbb{E}[X(T)] > S(\infty)$, so the expected final size $|\mathcal{S}_0| - \mathbb{E}[X(T)]$ is strictly smaller than the deterministic final size $S(0) - S(\infty)$.

## Depends on

- [Final-size relation (Kermack–McKendrick 1927)](../../kermack-mckendrick-sir-model/final-size.md)

## Expansion

The proof sandwiches a message-passing approximation between the two models: $\mathbb{E}[X(t)] \ge S_{\mathrm{mes}}(t) > S(t)$. On the complete graph, the message-passing system tracks, for each susceptible, the probability that no neighbour (held in a cavity state, unable to receive infection back) has transmitted to it; because it ignores the positive correlations between the infection histories of different neighbours, it underestimates the probability of escaping infection, which gives the first inequality, as in the Karrer–Newman argument. Rewriting the Kermack–McKendrick system per initially susceptible individual, $\dot s = -\beta s\,(|\mathcal{S}_0|\,i + |\mathcal{I}_0|e^{-\gamma t})$, shows that it counts infection pressure as if every susceptible could be infected by every other one, including by individuals it would itself have infected; this double counting makes the deterministic model infect faster than message passing, which gives the strict second inequality. The bound on recoveries follows from the Kolmogorov forward equation $\frac{d}{dt}\mathbb{E}[Z] = \gamma\,\mathbb{E}[Y]$ together with conservation of individuals, and the final-size statement follows by dominated convergence. This settles a long-standing conjecture that the deterministic SIR model always overestimates the stochastic epidemic, known before only for the SI and SIS cases.

## Sources

- Robert R. Wilkinson, Frank G. Ball, Kieran J. Sharkey, "The deterministic Kermack‒McKendrick model bounds the general stochastic epidemic", Journal of Applied Probability 53 (2016), 1031–1040, <https://doi.org/10.1017/jpr.2016.62>. Published version of arXiv:1602.01730, cited next; locators there refer to the arXiv version.
- Robert R. Wilkinson, Frank G. Ball, Kieran J. Sharkey, "The deterministic Kermack-McKendrick model bounds the general stochastic epidemic", arXiv:1602.01730 (2016), Section 1 (model), Section 2 (Theorem 1, Corollary 1, Lemmas 1 and 2, Theorem 2), <https://doi.org/10.48550/arXiv.1602.01730>.
