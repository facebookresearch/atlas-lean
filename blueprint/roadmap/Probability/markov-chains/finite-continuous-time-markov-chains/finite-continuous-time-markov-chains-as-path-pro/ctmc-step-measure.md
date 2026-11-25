# Law of one step of the chain construction

Let $Q$ be a [rate matrix](../rate-matrices-of-finite-continuous-time-markov-c/is-rate-matrix.md) on a
finite set $S$ with [jump matrix](ctmc-jump-matrix.md) $\Pi$. The law of one step $(\xi, E)$, with
$\xi : S \to S$ and $E \in \mathbb{R}$, is the product measure

$$\Bigl( \bigotimes_{i \in S} \Pi(i, \cdot) \Bigr) \otimes \operatorname{Exp}(1):$$

the coordinates $\xi(i)$ are independent with $\xi(i) \sim \Pi(i, \cdot)$, and $E$ is an
independent exponential clock of rate $1$.
