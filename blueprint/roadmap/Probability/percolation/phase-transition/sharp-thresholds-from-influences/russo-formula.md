# Russo's formula

Let $E$ be a finite set and let $A \subseteq \{0, 1\}^E$ be an [increasing](../../../correlation-inequalities/harris-fkg-bk/increasing-events-and-the-fkg-lattice-condition/is-increasing.md) event. For real $p$ write $\mathbb{P}_p(A) = \sum_{\omega \in A} \prod_{e \in E} p^{\omega_e} (1 - p)^{1 - \omega_e}$ for the [weight](../../../correlation-inequalities/harris-fkg-bk/russo-s-formula-and-pivotal-coordinates/prob.md) of $A$, the probability of $A$ under independent Bernoulli($p$) coordinates when $p \in [0, 1]$. For every real $p \notin \{0, 1\}$,

$$\frac{d}{dp} \mathbb{P}_p(A) = \frac{1}{p(1 - p)} \sum_{e \in E} \Big(\mathbb{P}_p(A \cap \{\omega_e = 1\}) - \mathbb{P}_p(\omega_e = 1)\, \mathbb{P}_p(A)\Big).$$

The same identity holds for every event: [Russo's formula, covariance form, for an arbitrary event](../../../correlation-inequalities/harris-fkg-bk/russo-s-formula-and-pivotal-coordinates/has-deriv-at-prob-eq-sum-cov.md).
