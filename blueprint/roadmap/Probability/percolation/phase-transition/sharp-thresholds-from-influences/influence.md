# Influence of an edge on an event

Let $E$ be a finite set, $A \subseteq \{0, 1\}^E$ an event, $e \in E$ and $p \in \mathbb{R}$. The influence of $e$ on $A$ is

$$I_e^p(A) = \sum_{\omega \,:\, e \text{ pivotal for } A \text{ at } \omega} \ \prod_{f \in E} p^{\omega_f} (1 - p)^{1 - \omega_f},$$

the [weight](../../../correlation-inequalities/harris-fkg-bk/russo-s-formula-and-pivotal-coordinates/pivotal-prob.md) of the event that $e$ is [pivotal](../../../correlation-inequalities/harris-fkg-bk/russo-s-formula-and-pivotal-coordinates/is-pivotal.md) for $A$. For $p \in [0, 1]$ it is $\mathbb{P}_p(e \text{ is pivotal for } A)$ under the product measure with independent Bernoulli($p$) coordinates.

For $p = 1/2$ this is, up to normalisation, the [influence of a coordinate on the uniform Boolean cube](../../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/README.md) of Fourier analysis.
