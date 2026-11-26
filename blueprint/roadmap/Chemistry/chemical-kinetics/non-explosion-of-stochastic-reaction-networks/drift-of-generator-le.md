# A generator bound at a state gives the one-step drift condition

Let $N$ be a [stochastic chemical reaction network](stochastic-crn.md) with a finite set $S$ of
species and a finite set of reactions, [generator](generator.md) $L$,
[holding rate](hold-rate.md) $q$ and [jump kernel](jump-pmf.md) $P$. Let
$V : \mathbb{N}^S \to [0, \infty)$, $c \ge 0$ and $x \in \mathbb{N}^S$. If $L V(x) \le c\, V(x)$,
then

$$q(x) \int V \, dP(x, \cdot) \le \bigl(q(x) + c\bigr)\, V(x).$$

The integral is the lower Lebesgue integral of $V$ against $P(x, \cdot)$, here the finite sum
$\sum_y P(x, \{y\})\, V(y)$, the mean of $V$ at the next state; $q(x)$ and $q(x) + c$ are positive.
This is the one-step drift condition at $x$ for the jump–hold chain with holding rates $q$ and jump
kernel $P$.
