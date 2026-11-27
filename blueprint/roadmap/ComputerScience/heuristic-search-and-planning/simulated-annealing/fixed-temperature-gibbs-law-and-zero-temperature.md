# Fixed-temperature Gibbs law and zero-temperature concentration

Let $V$ be a real function on a finite nonempty set $S$ and, for $T > 0$, let $\pi_T(x) = \exp(-V(x)/T)/Z_T$ with
$Z_T = \sum_{y \in S} \exp(-V(y)/T)$ be the Gibbs law at temperature $T$. For a symmetric proposal $Q$, the
Metropolis–Hastings chain with target $\pi_T$ accepts a proposed move from $x$ to $y$ with probability
$\min\{1, \exp(-(V(y) - V(x))/T)\}$, which is the acceptance rule of simulated annealing at the fixed temperature $T$;
so $\pi_T$ satisfies detailed balance for that chain and is stationary for it. As $T \to 0^+$, $\pi_T(S^*) \to 1$, where
$S^*$ is the set of global minimizers of $V$, and $\pi_T$ converges to the uniform law on $S^*$: for $x \notin S^*$,
$\pi_T(x)/\pi_T(s^*) = \exp(-(V(x) - \min V)/T) \to 0$ for any $s^* \in S^*$. The statement concerns the chain at a fixed
temperature and says nothing about the time-inhomogeneous annealing chain.

## Depends on

- [Metropolis–Hastings step](../../machine-learning/bayesian-inference-and-sampling/markov-chain-monte-carlo/mh-step.md)

## Proof depends on

- [Detailed balance for Metropolis–Hastings](../../machine-learning/bayesian-inference-and-sampling/markov-chain-monte-carlo/mh-detailed-balance.md)
- [Detailed balance gives a stationary distribution](../../machine-learning/bayesian-inference-and-sampling/markov-chain-monte-carlo/bind-eq-of-detailed-balance.md)

## Related topics

- [Hajek's cooling-schedule theorem](hajek-s-cooling-schedule-theorem.md)

## Sources

- D. A. Levin, Y. Peres and E. L. Wilmer, *Markov Chains and Mixing Times*, American Mathematical Society (author copy),
  Section 3.2.1: the Metropolis chain for a symmetric base chain, its acceptance probability $\min\{1, \pi(y)/\pi(x)\}$
  and detailed balance, and Example 3.2, where $\pi_\lambda \propto \lambda^{f}$ concentrates on the maximizers of $f$ as
  $\lambda \to \infty$; take $f = -V$ and $\lambda = e^{1/T}$.
  <https://pages.uoregon.edu/dlevin/MARKOV/markovmixing.pdf>
