# Russo's formula for the finite projection of an increasing event, derivative form

Let $E$ be a set, $A \subseteq \{0, 1\}^E$ an [increasing](../../correlation-inequalities/harris-fkg-bk/increasing-events-and-the-fkg-lattice-condition/is-increasing.md) event, $F \subseteq E$ finite, and $A_F = \{\omega|_F : \omega \in A\} \subseteq \{0, 1\}^F$ its projection. For real $q$ let $\mathbb{P}_q(A_F) = \sum_{\eta \in A_F} \prod_{e \in F} q^{\eta_e} (1 - q)^{1 - \eta_e}$ be its [weight](../../correlation-inequalities/harris-fkg-bk/russo-s-formula-and-pivotal-coordinates/prob.md). For every $q \in \mathbb{R}$,

$$\frac{d}{dq} \mathbb{P}_q(A_F) = \sum_{e \in F} I_e^q(A_F),$$

where $I_e^q(A_F)$ is the [weight of the event that $e$ is pivotal](../../correlation-inequalities/harris-fkg-bk/russo-s-formula-and-pivotal-coordinates/pivotal-prob.md) for $A_F$.
