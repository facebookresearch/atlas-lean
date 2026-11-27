# Concentrability coefficient over admissible distributions

The concentrability coefficient of a batch data distribution $\mu$ over state-action pairs is the largest ratio $\nu(s,a)/\mu(s,a)$ over all distributions $\nu$ that some policy induces at some time step; when it is a finite $C$, data drawn from $\mu$ covers every policy's state-action distribution up to the factor $C$.

**Setting.** An MDP $M=(S,A,P,R,\gamma,\eta_1)$ has a finite state set $S$, a finite action set $A$, transition function $P:S\times A\to\Delta(S)$, reward function $R:S\times A\to[0,R_{\max}]$, discount $\gamma\in[0,1)$ and initial state distribution $\eta_1$. A trajectory from $\eta_1$ under a policy $\pi$ is $s_1\sim\eta_1$, $a_1\sim\pi$, $s_2\sim P(s_1,a_1)$, and so on. The batch data distribution is a probability distribution $\mu$ on $S\times A$.

**Admissible distributions (Chen and Jiang, Definition 1).** A distribution $\nu\in\Delta(S\times A)$ is admissible in $M$ if there are a time step $h$ and a policy $\pi$, possibly non-stationary and stochastic, such that

$$
\nu(s,a)=\Pr\big[s_h=s,\ a_h=a\ \big|\ s_1\sim\eta_1,\ \pi\big]\quad\text{for all }(s,a).
$$

**Concentrability coefficient (Chen and Jiang, Assumption 1).** The data distribution $\mu$ satisfies concentrability with constant $C<\infty$ if

$$
\frac{\nu(s,a)}{\mu(s,a)}\le C\quad\text{for every admissible }\nu\text{ and every }(s,a)\in S\times A,
$$

The source does not discuss pairs with $\mu(s,a)=0$; read the ratio there as $0$ when $\nu(s,a)=0$ and as $+\infty$ otherwise, as for Munos's coefficients. The concentrability coefficient of $\mu$ is the smallest such $C$, the supremum of these ratios, an extended nonnegative real.

A finite coefficient gives the norm transfer $\|g\|_{2,\nu}\le\sqrt C\,\|g\|_{2,\mu}$ for every $g:S\times A\to\mathbb R$ and admissible $\nu$, where $\|g\|_{2,\nu}^2=\mathbb E_{(s,a)\sim\nu}[g(s,a)^2]$ (Chen and Jiang, Lemma 12); this is how the coefficient enters [sample-complexity bounds for fitted Q-iteration](fitted-q-iteration-error-bound.md). The coefficient depends on the dynamics and $\eta_1$, not only on $\mu$; Chen and Jiang (§4) discuss its necessity and examples where it is small.

This is a different coefficient from the two of Munos on approximate value iteration: the [transition concentration coefficient](../greedy-policies-of-approximate-values/transition-concentration-coefficient.md) bounds one-step transition probabilities against a state distribution, and the [future distribution coefficient](../greedy-policies-of-approximate-values/the-future-distribution-coefficient.md) bounds the state distribution after exactly $m$ steps of deterministic decision rules from a given initial law. The coefficient here compares state-action distributions, allows stochastic non-stationary policies, and takes the worst case over all time steps at once. The [single-policy concentrability coefficient](single-policy-concentrability.md) replaces the supremum over policies by one comparator policy.

## Depends on

- [Markov decision process](../../../heuristic-search-and-planning/value-iteration/mdp.md)
- [Stochastic Markov decision process](../../../heuristic-search-and-planning/value-iteration/stochastic.md)
- [History-dependent randomized policies and trajectory laws](../../../heuristic-search-and-planning/markov-decision-processes/history-dependent-randomized-policies-and-trajectory-laws.md)

## Proof depends on

None. This page is a definition.

## Expansion

The norm transfer follows termwise: $\|g\|_{2,\nu}^2=\sum_{(s,a)}g(s,a)^2\nu(s,a)\le C\sum_{(s,a)}g(s,a)^2\mu(s,a)$. Chen and Jiang adopt this simplified form of Munos's coefficient so that their bounds are a priori; refinements that use the function class are discussed in their §6 and Appendix G.

## Sources

- J. Chen and N. Jiang, *Information-Theoretic Considerations in Batch Reinforcement Learning*, Proceedings of the 36th International Conference on Machine Learning, PMLR 97:1042–1051 (2019). [arXiv:1905.00360v1](https://arxiv.org/abs/1905.00360v1), §2.1–§2.2 (setting), §3.2, Definition 1 and Assumption 1; Appendix C, Lemma 12.
- R. Munos, *Performance Bounds in Lp-norm for Approximate Value Iteration*, SIAM Journal on Control and Optimization 46(2), 541–561 (2007), [DOI 10.1137/040614384](https://doi.org/10.1137/040614384), §5.1, Definition 5.1, for comparison.
