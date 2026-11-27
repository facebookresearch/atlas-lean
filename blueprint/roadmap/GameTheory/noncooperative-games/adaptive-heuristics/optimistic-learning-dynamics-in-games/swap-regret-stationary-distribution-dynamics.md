# Internal and swap regret minimization via stationary distributions

Let a learner choose distributions $x^t \in \Delta_n$ against losses $\ell^t \in [0,1]^n$. For a map $\phi : [n] \to [n]$, the swap regret against $\phi$ is $\sum_{t} \sum_a x^t(a)\,\bigl(\ell^t(a) - \ell^t(\phi(a))\bigr)$, and the swap regret is the maximum over all $\phi$. The internal regret is the maximum over the maps $\phi$ that move a single action $a$ to an action $b \ne a$ and fix all others. The Blum–Mansour construction runs $n$ external-regret learners $\mathcal{A}_1, \dots, \mathcal{A}_n$, one per row, combines their recommendations $q_1^t, \dots, q_n^t \in \Delta_n$ into the row-stochastic matrix $Q^t$ with rows $q_a^t$, plays a stationary distribution $x^t = x^t Q^t$, and feeds learner $\mathcal{A}_a$ the scaled loss $x^t(a)\, \ell^t$; this bounds the swap regret by the sum of the learners' external regrets. The conversion from external to internal regret given independently by Stoltz and Lugosi is different: it runs a single external-regret algorithm over the $n(n-1)$ pair experts $a \to b$, where expert $a \to b$ plays $x$ with the mass of $a$ moved to $b$, and plays a fixed point $x^t$ of the mixture of these modified strategies under the algorithm's weights.

## Depends on

- [Swap regret](../../../not-yet-classified/part-02/regret/swap-regret.md)
- [External regret](../../../not-yet-classified/part-02/regret/external-regret.md)
- [Existence of a stationary play](../../../not-yet-classified/part-02/regret-blum-mansour/exists-is-stationary-play.md)
- [Regret against a family of modification rules; internal regret](../../../../ComputerScience/machine-learning/online-learning-and-boosting/swap-and-internal-regret/modification-rule-regret-and-internal-regret.md)

## Sources

- A. Blum, Y. Mansour, "From External to Internal Regret", Journal of Machine Learning Research 8 (2007), Sections 1.1 and 3.
- G. Stoltz, G. Lugosi, "Internal regret in on-line portfolio selection", Machine Learning 59 (2005).
