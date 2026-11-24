# Influence on an indicator is the pivotal probability

Let $E$ be a finite set, $\nu$ weights $\nu_e : \{0, 1\} \to \mathbb{R}$, $A \subseteq \{0, 1\}^E$ and $e \in E$. Then

$$\mathrm{Inf}_e(1_A) = \mathbb{E}_\nu\big[1_{\{\omega \,:\, e \text{ is pivotal for } A \text{ at } \omega\}}\big],$$

where $e$ is pivotal for $A$ at $\omega$ when exactly one of $\omega^{e \to 1}$ and $\omega^{e \to 0}$ lies in $A$. For a [product probability weight](is-prob-weight.md) the right side is the probability that $e$ is pivotal for $A$.
