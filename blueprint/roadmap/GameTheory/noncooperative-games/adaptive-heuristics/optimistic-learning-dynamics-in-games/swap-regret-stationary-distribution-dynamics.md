# Internal and swap regret minimization via stationary distributions

Let a learner choose distributions $x^t \in \Delta_n$ against losses $\ell^t \in [0,1]^n$. For a map $\phi : [n] \to [n]$, the swap regret against $\phi$ is $\sum_{t} \sum_a x^t(a)\,\bigl(\ell^t(a) - \ell^t(\phi(a))\bigr)$, and the swap regret is the maximum over all $\phi$. The Blum–Mansour (and Stoltz–Lugosi) construction runs $n$ external-regret learners $\mathcal{A}_1, \dots, \mathcal{A}_n$, combines their recommendations $q_1^t, \dots, q_n^t \in \Delta_n$ into the row-stochastic matrix $Q^t$, plays a stationary distribution $x^t = x^t Q^t$, and feeds learner $\mathcal{A}_a$ the scaled loss $x^t(a)\, \ell^t$.

## Depends on

- [Swap regret](../../../not-yet-classified/part-02/regret/swap-regret.md)
- [External regret](../../../not-yet-classified/part-02/regret/external-regret.md)
- [Existence of a stationary play](../../../not-yet-classified/part-02/regret-blum-mansour/exists-is-stationary-play.md)

## Sources

- A. Blum, Y. Mansour, "From External to Internal Regret", Journal of Machine Learning Research 8 (2007).
- G. Stoltz, G. Lugosi, "Internal regret in on-line portfolio selection", Machine Learning 59 (2005).
