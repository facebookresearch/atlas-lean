# Law of one step of the jump–hold chain

Let $S$ be a set with a σ-algebra and $P$ a jump kernel on $S$: for each $x \in S$, a probability
mass function $P(x, \cdot)$ on $S$, viewed as the probability measure
$B \mapsto \sum_{y \in B} P(x, y)$ on the measurable sets $B \subseteq S$. The law of one step
$(\xi, E)$, made of a map $\xi : S \to S$ and a clock $E \in \mathbb{R}$, is the product measure

$$\mu_P = \Bigl( \bigotimes_{x \in S} P(x, \cdot) \Bigr) \otimes \operatorname{Exp}(1),$$

for the product σ-algebra on the maps $S \to S$ and the Borel σ-algebra on $\mathbb{R}$. Here
$\operatorname{Exp}(1)$ is the exponential law of rate $1$, with density $e^{-t}$ for $t \ge 0$ and
$0$ for $t < 0$. The measure $\mu_P$ is a probability measure: under it the coordinates $\xi(x)$,
$x \in S$, are independent with $\xi(x) \sim P(x, \cdot)$, and the clock $E$ is independent of $\xi$
with law $\operatorname{Exp}(1)$.
