# Strong Markov property of an i.i.d. step sequence

Let $S$ be a measurable space, and give the steps $(\xi, E) \in S^S \times \mathbb{R}$ (maps
$S \to S$ and real clock values) the product of the product σ-algebra on maps and the Borel
σ-algebra on $\mathbb{R}$. Let $\nu$ be a probability measure on the steps, for example the
[law of one step of the jump–hold chain](../non-explosion-of-stochastic-reaction-networks/step-measure.md),
and let $\mathbb{P} = \nu^{\otimes \mathbb{N}}$ be the product measure on step sequences
$\omega = (\omega_n)_{n \in \mathbb{N}}$, under which the steps are i.i.d. with law $\nu$. Let
$\tau$ be a [stopping time of the step sequence](is-step-stopping-time.md) that is measurable
(every level set $\{\tau = n\}$, $n \in \mathbb{N} \cup \{\infty\}$, is measurable), let $C$ be a
measurable set of step sequences [determined before $\tau$](is-determined-before.md), and let $B$
be any measurable set of step sequences. Write $F = \{\omega : \tau(\omega) < \infty\}$,
$\theta_\tau \omega$ for the [steps after $\tau$](shift-at.md) and
$\theta_\tau^{-1}(B) = \{\omega : \theta_\tau \omega \in B\}$. Then

$$\mathbb{P}(F \cap C \cap \theta_\tau^{-1}(B)) = \mathbb{P}(F \cap C)\, \mathbb{P}(B) .$$

So, when $\mathbb{P}(F) > 0$, under $\mathbb{P}$ conditioned on $F$ the steps after $\tau$ have the
law $\mathbb{P}$ of the whole sequence and are independent of the event $C$.
