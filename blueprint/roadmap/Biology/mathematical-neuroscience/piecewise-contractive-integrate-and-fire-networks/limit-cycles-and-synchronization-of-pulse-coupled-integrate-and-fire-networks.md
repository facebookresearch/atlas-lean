# Limit cycles and synchronization of integrate-and-fire networks via piecewise contractive return maps

**Model.** A network of $n$ identical leaky integrate-and-fire neurons with membrane potentials $V_i$ evolves below threshold $\theta > 0$ by $\dot V_i = -\gamma V_i + K$, relaxing towards $\beta = K/\gamma > \theta$. When neurons reach $\theta$, the set $J$ of all neurons that fire (spontaneously or through an avalanche of instantaneous excitations, each neuron firing at most once) is reset to $0$, and every other neuron jumps by $\sum_{j\in J}H_{ji}$; $H_{ji} > 0$ is excitatory and $H_{ji} < 0$ inhibitory. Hypotheses: (H1) potentials are bounded below by some $\alpha < 0$; (H2) a neuron receiving simultaneous excitation and inhibition fires if the excitation alone reaches threshold; (H3) $\beta < \beta_+(\alpha) = \tfrac12(\alpha + 2\theta + \sqrt{\alpha^2 + 4\theta^2})$ and $\min_{j\neq i}|H_{ji}| > \epsilon := \tfrac12\big(\sqrt{(\beta-\theta)^2 + 4(\beta-\theta)(\beta-\alpha)} - (\beta-\theta)\big)$; (H4) Dale's principle: each neuron is purely excitatory or purely inhibitory.

The dynamics are equivalent to a piecewise continuous return map $\rho$ on the Poincaré section $\Sigma$ of states just after a firing, defined on the atoms $\Sigma_J$ (indexed by the set $J$ of firing neurons) by $\rho_i(\mathbf{V}) = 0$ for $i \in J$ and $\rho_i(\mathbf{V}) = \max\{\alpha, \phi_i^{\bar t(\mathbf{V})}(\mathbf{V}) + \sum_{j\in J}H_{ji}\}$ otherwise, with $\phi^t$ the subthreshold flow and $\bar t$ the next firing time.

**Theorem.**
1. (Not globally contractive.) Under (H1)–(H2) there is an open region of interaction values for which $\Sigma$ is not a contractive zone for $\rho$ with respect to the natural partition, in any norm.
2. (Piecewise contraction.) Under (H1)–(H4), if at least one neuron is inhibitory, there is an adapted metric and partition of $\Sigma$ for which $\rho$ is piecewise contractive; the set $\Sigma^* = \overline{\rho(\mathcal{C}_{\bar c})}$, with $\mathcal{C}_c = \{\alpha \le V_i \le c\}$, is a forward-invariant contractive zone that absorbs every orbit after at most $p+1$ steps, where $\alpha + p\min_{j\neq i}|H_{ji}| \ge \theta$.
3. (Limit cycles.) Consequently, with an inhibitory neuron and strong enough interactions, the stable asymptotic dynamics are supported on at most countably many limit cycles attracting all orbits that eventually avoid the discontinuity set.
4. (Synchronization.) Under (H1), if all neurons are excitatory and

$$n \ge \Big\lceil \frac{\theta}{\min_{j\neq i}H_{ji}} \Big\rceil^2,$$

the network globally synchronizes (all neurons fire together after a transient of explicit bounded length); a purely excitatory network whose orbit enters $\Sigma^*$ synchronizes regardless of its size. For two neurons with $H_{12} = H_{21} \in (0,\theta)$ there are non-synchronized period-two orbits, so a size condition is needed.

## Expansion

Between firings the subthreshold flow is a contraction towards $\beta$, but resets and instantaneous excitatory avalanches create discontinuities and can expand distances, which is why global contraction fails. Strong inhibition forces every potential down to the floor $\alpha$ or into a bounded box after finitely many firings, inside which the return map contracts on each continuity piece; piecewise contractive maps have asymptotic dynamics supported on periodic orbits generically, hence limit cycles. In a large excitatory network the cumulative excitation of any firing is enough to push all neurons over threshold within a bounded number of firings, producing one synchronous avalanche.

## Sources

- E. Catsigeras and P. Guiraud, "Integrate and fire neural networks, piecewise contractive maps and limit cycles", Journal of Mathematical Biology 67 (2012), 609–655, <https://doi.org/10.1007/s00285-012-0560-7>; numbering as in arXiv:1011.1525: model equations and hypotheses (H1)–(H4) (Sections 2–3), Theorem 1, Proposition 2.2, Theorem 2, Propositions 3.6, 3.8, 3.9, Theorem 3, Theorem 4 and Propositions 4.2–4.3.
