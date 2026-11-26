# Exact tau-splitting algorithm for the chemical master equation

**Setting.** A stochastic reaction network has species counts $S_t \in \mathbb{N}^s$ and reactions $R_1, \dots, R_d$; reaction $R_i$ has input species $I_i$, stoichiometry vector $O_i \in \mathbb{Z}^s$ (positive part $O_i^{+}$, negative part $O_i^{-}$) and a mass-action rate $\rho_i(S)$, and under the chemical master equation it fires in $[t, t + dt)$ with probability $\rho_i(S_t)\,dt + O(dt^2)$. Let $\mathbb{P}_T$ be the law of $S_T$ given $S_0$.

**Tau-leaping steps.** A step over $[t_0, t_1)$ with initial state $S_{t_0}$ records, for each reaction, a putative count $e_i$ and rate bounds $l_i \le \rho_i(S_{t_0}) < u_i$, sampled from a coupling of the Poisson laws $\mathrm{Pois}(\gamma(t_1 - t_0))$, $\gamma > 0$, that makes the count a nondecreasing step function of $\gamma$; $[l_i, u_i)$ is the step of that function containing $\rho_i(S_{t_0})$, so every constant rate in $[l_i, u_i)$ would have produced the same count $e_i \sim \mathrm{Pois}(\rho_i(S_{t_0})(t_1 - t_0))$. Tuples for different reactions are independent, and a step is independent of earlier steps given $S_{t_0}$.

**Exact stopping condition.** With $\delta_i = \min(e_i, 1)$, a step is accepted (STOP) if and only if, for every $i$,

$$\rho_i\Big(S_{t_0} + \sum_j e_j O_j^{+}\Big) < u_i \qquad\text{and}\qquad \rho_i\Big(S_{t_0} + \sum_j e_j O_j^{-} - \delta_i O_i^{-}\Big) \ge l_i ;$$

otherwise the step is split at the midpoint into a step on the first half and a precursor on the second half, which is resampled from the true state at the midpoint, and both halves are processed recursively.

**Statement.** If $S_t[k]$ is bounded in probability for all $t$ and $k$, the tau-splitting algorithm started from $S_0$ returns a sample with law exactly $\mathbb{P}_T$. Almost surely only finitely many steps fail the stopping condition, so the recursion terminates; and the depth-$d$ truncation (accept every step at depth $d$) has law $\mathbb{P}_T^{d} \to \mathbb{P}_T$ in $L^1$ as $d \to \infty$.

## Depends on

- [Gillespie direct method (stochastic simulation algorithm)](../gillespie-direct-method.md)

## Expansion

The two inequalities bound every rate that can occur along any ordering of the $e_j$ firings inside the step: adding only products gives the largest possible input counts, removing only reactants (but not the last firing of $R_i$ itself) gives the smallest. If all such rates stay inside $[l_i, u_i)$, the Poisson-coupled counts of the true time-varying process equal the constant-rate counts, so the accepted step has exactly the master-equation law of the increment. Splitting with conditional resampling preserves the joint law, and the finiteness of unstable nodes gives termination.

## Sources

- R. Solan and G. Getz, An exact tau-leaping method, arXiv (2025). <https://doi.org/10.48550/arXiv.2509.12631> (Theorem 3.7, Definition 3.8, Properties 3.5 and 3.6, Lemmas 3.10 and 3.12.)
