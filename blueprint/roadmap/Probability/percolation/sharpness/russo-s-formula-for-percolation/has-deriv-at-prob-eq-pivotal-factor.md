# Russo's formula, pivotal-factor form

Let $E$ be a finite set and $A \subseteq \{0, 1\}^E$ an [increasing](../../../correlation-inequalities/harris-fkg-bk/increasing-events-and-the-fkg-lattice-condition/is-increasing.md) event, and for real $p$ let $\mathbb{P}_p(A) = \sum_{\omega \in A} w_p(\omega)$ with $w_p(\omega) = \prod_{e \in E} p^{\omega_e} (1 - p)^{1 - \omega_e}$ (the [weight](../../../correlation-inequalities/harris-fkg-bk/russo-s-formula-and-pivotal-coordinates/prob.md) of $A$). For $0 < p < 1$, the function $p \mapsto \mathbb{P}_p(A)$ is differentiable at $p$ with

$$\frac{d}{dp} \mathbb{P}_p(A) = \frac{1}{p(1 - p)} \sum_{e \in E} \mathbb{E}_p\big[\mathbf{1}_A\, (\omega_e - p)\big], \qquad \mathbb{E}_p\big[\mathbf{1}_A\, (\omega_e - p)\big] = \sum_{\omega \in A} (\omega_e - p)\, w_p(\omega).$$
