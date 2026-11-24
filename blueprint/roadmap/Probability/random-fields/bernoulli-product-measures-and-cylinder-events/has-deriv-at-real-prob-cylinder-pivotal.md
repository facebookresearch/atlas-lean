# Russo's formula for the finite projection of an increasing event

Let $E$ be a set, $A \subseteq \{0, 1\}^E$ an [increasing](../../correlation-inequalities/harris-fkg-bk/increasing-events-and-the-fkg-lattice-condition/is-increasing.md) event, $F \subseteq E$ finite and $A_F = \{\omega|_F : \omega \in A\}$ its projection. For every $q \in \mathbb{R}$, the [weight](../../correlation-inequalities/harris-fkg-bk/russo-s-formula-and-pivotal-coordinates/prob.md) $q \mapsto \mathbb{P}_q(A_F) = \sum_{\eta \in A_F} \prod_{e \in F} q^{\eta_e} (1 - q)^{1 - \eta_e}$ is differentiable at $q$ with derivative

$$\sum_{e \in F} I_e^q(A_F),$$

the sum over $e \in F$ of the [weight of the event that $e$ is pivotal](../../correlation-inequalities/harris-fkg-bk/russo-s-formula-and-pivotal-coordinates/pivotal-prob.md) for $A_F$.

## Sources

- Lucio Russo, *On the critical percolation probabilities*, Z. Wahrsch. Verw. Gebiete 56 (1981), no. 2, 229–237,
  DOI 10.1007/bf00535742.
