# Influence of an event as the influence of its indicator

Let $E$ be a finite set, $p$ a real number, $A \subseteq \{0, 1\}^E$ and $e \in E$. The pivotal weight $\mathrm{Inf}_e(A) = \sum_{\omega:\ e \text{ pivotal for } A} \prod_{j} w_p(\omega_j)$, with $w_p(1) = p$ and $w_p(0) = 1 - p$, equals the [influence](../../osss-inequality-for-decision-trees/infl.md) of the indicator $1_A$:

$$\mathrm{Inf}_e(A) = \mathbb{E}_p\big\lvert 1_A(\omega^{e \to 1}) - 1_A(\omega^{e \to 0})\big\rvert.$$

Here $e$ is pivotal for $A$ at $\omega$ when exactly one of $\omega^{e \to 1}$ and $\omega^{e \to 0}$ lies in $A$.
