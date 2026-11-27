# PAC bound under low witness rank

With a realizable finite model class and Bellman-dominating test functions, an optimistic model-elimination algorithm finds an $\varepsilon$-optimal policy with probability $1-\delta$ from $\tilde O\big(\frac{H^3 \mathrm{W}_\kappa^2 K}{\kappa^2\varepsilon^2}\log\frac{T|\mathcal{F}||\mathcal{M}|}{\delta}\big)$ trajectories, where $\mathrm{W}_\kappa$ is the witness rank and $K$ the number of actions.

**Assumptions.** A contextual decision process with horizon $H$, $K$ actions, rewards with $\sum_h r_h \le 1$, and a finite model class $\mathcal{M}$ that contains the true model $M^\star$ (Assumption 1, realizability). The finite test class $\mathcal{F}$ is symmetric, bounded by $2$, and satisfies Bellman domination (Assumption 2). $\mathrm{W}_\kappa = \max_h \mathrm{W}(\kappa,\beta,\mathcal{M},\mathcal{F},h)$ is the [witness rank](witness-rank.md).

**Algorithm (optimistic model elimination, the source's Algorithm 1).** Keep a version space $\mathcal{M}_t$, starting from $\mathcal{M}$. In round $t$: pick the optimistic model $M^t = \arg\max_{M\in\mathcal{M}_{t-1}} v_M$ and run $\pi^t = \pi_{M^t}$ for $n_e$ trajectories to estimate its value $\hat v^{\pi^t}$. Terminate and output $\pi^t$ if $|\hat v^{\pi^t} - v_{M^t}| \le \varepsilon/2$. Otherwise find a step $h_t$ with estimated average Bellman error $\hat{\mathcal{E}}_B(M^t, M^t, h_t) \ge \varepsilon/(4H)$. Collect $n$ trajectories following $\pi^t$ except for a uniformly random action at step $h_t$, and estimate $\widehat{\mathcal{W}}(M^t, M', h_t)$ for all $M'$ by importance weighting. Keep the models with $\widehat{\mathcal{W}}(M^t, M, h_t) \le \phi$.

**Theorem.** Under Assumptions 1 and 2, for any $\varepsilon, \delta, \kappa \in (0,1]$, set $\phi = \frac{\kappa\varepsilon}{48H\sqrt{\mathrm{W}_\kappa}}$ and $T = H\mathrm{W}_\kappa \log(\beta/(2\phi))/\log(5/3)$. Run the algorithm with $n_e = \Theta(H^2\log(HT/\delta)/\varepsilon^2)$ and $n = \Theta(H^2 K \mathrm{W}_\kappa \log(T|\mathcal{M}||\mathcal{F}|/\delta)/(\kappa\varepsilon)^2)$. Then with probability at least $1-\delta$ it outputs a policy $\pi$ with $v^\pi \ge v^\star - \varepsilon$, after collecting at most

$$
\tilde O\Big(\frac{H^3 \mathrm{W}_\kappa^2 K}{\kappa^2 \varepsilon^2} \log\frac{T|\mathcal{F}||\mathcal{M}|}{\delta}\Big)
$$

trajectories.

**Scope.** This is a sample-complexity result: the optimistic step is a constrained optimization over surviving models with bilinear, non-convex constraints even in the tabular case, and the source gives no efficient implementation. The bound needs realizability of the whole model, $\log|\mathcal{M}|$ rather than the log-size of the induced $Q$-function class, and scales with $K$ through the uniform action at step $h_t$. A variant using a Scheffé-type estimator removes the dependence on $|\mathcal{F}|$, giving $\tilde O\big(\frac{H^3\mathrm{W}_\kappa^2K}{\kappa^2\varepsilon^2}\log\frac{T|\mathcal{M}|}{\delta}\big)$ (Theorem 7). A doubling scheme adapts to unknown $\kappa$ and $\mathrm{W}_\kappa$.

## Depends on

- [Witness rank](witness-rank.md)

## Proof depends on

- [Two-sided Hoeffding inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-abs-avg-sub-ge-le.md)

## Expansion

A finite-horizon simulation lemma writes $v_{M^t} - v^{\pi^t}$ as the sum over $h$ of average Bellman errors $\mathcal{E}_B(M^t, M^t, h)$. So if the round does not terminate, some step has a large Bellman error. By Bellman domination the witnessed misfit $\mathcal{W}(M^t, M^t, h_t)$ is then large and $M^t$ is eliminated, while $M^\star$, with zero misfit, survives. Concentration (Hoeffding's inequality for the value estimates, uniform deviation bounds over $\mathcal{F}$ and $\mathcal{M}$ for the misfit estimates) makes these tests reliable. The witness-rank factorization $A = UV^{\mathsf T}$ turns the rounds into a sequence of linear constraints on $V$-vectors in dimension $\mathrm{W}_\kappa$. A volume argument for the minimum-volume enclosing ellipsoid (adapted from Jiang et al. 2017) bounds the number of non-terminal rounds at each step by $O(\mathrm{W}_\kappa\log(\beta/\phi))$.

A complete expansion adds pages for the finite-horizon simulation lemma $v_M - v^{\pi_M} = \sum_h \mathcal{E}_B(M,M,h)$ (Lemma 10), the volume reduction for minimum-volume enclosing ellipsoids used to count rounds (Lemma 9, from Jiang et al. 2017), and the deviation bounds for the importance-weighted misfit estimates and the Bellman-error estimates (Lemmas 12–13).

## Sources

- W. Sun, N. Jiang, A. Krishnamurthy, A. Agarwal and J. Langford, "Model-based RL in Contextual Decision Processes: PAC bounds and Exponential Improvements over Model-free Approaches", Conference on Learning Theory (COLT 2019), PMLR 99:2898–2933. Numbers from arXiv:1811.08540v3: Algorithm 1 with Eqs. (5)–(6) and the computational discussion, Theorem 6, Theorem 7, Appendix A (Lemmas 9–17), Appendix F (unknown witness rank). <https://arxiv.org/abs/1811.08540v3>
