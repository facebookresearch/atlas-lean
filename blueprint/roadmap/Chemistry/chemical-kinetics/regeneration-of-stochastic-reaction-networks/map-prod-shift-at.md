# Strong Markov property at an almost surely finite stopping time

Let $S$ be a measurable space, and give the steps $(\xi, E) \in S^S \times \mathbb{R}$ (maps
$S \to S$ and real clock values) the product of the product σ-algebra on maps and the Borel
σ-algebra on $\mathbb{R}$. Let $\nu$ be a probability measure on the steps and
$\mathbb{P} = \nu^{\otimes \mathbb{N}}$ the product measure on step sequences
$\omega = (\omega_n)_{n \in \mathbb{N}}$, under which the steps are i.i.d. with law $\nu$. Let
$\tau$ be a [stopping time of the step sequence](is-step-stopping-time.md) that is measurable
(every level set $\{\tau = n\}$, $n \in \mathbb{N} \cup \{\infty\}$, is measurable) and almost
surely finite, $\mathbb{P}(\tau = \infty) = 0$. Let $G$ be a measurable map from step sequences to
a measurable space that is determined before $\tau$: for every $n \in \mathbb{N}$, if
$\tau(\omega) = n$ and $\omega'_i = \omega_i$ for all $i < n$, then $G(\omega') = G(\omega)$. Then
the joint law of $G$ and the [steps after $\tau$](shift-at.md) $\theta_\tau \omega$ is the
product of the law of $G$ and $\mathbb{P}$:

$$\mathbb{P} \circ (G, \theta_\tau)^{-1} = (\mathbb{P} \circ G^{-1}) \otimes \mathbb{P} .$$

So the steps after $\tau$ have the law $\mathbb{P}$ of the whole sequence and are independent of
$G$.
