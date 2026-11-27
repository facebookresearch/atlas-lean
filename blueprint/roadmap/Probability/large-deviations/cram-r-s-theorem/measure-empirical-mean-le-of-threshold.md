# Chernoff bound for the empirical mean of real-valued i.i.d. variables

Let $\mu$ be a probability measure, let $X_0, X_1, \dots$ be measurable, independent real random
variables, each identically distributed with $X_0$, and let $t, a \in \mathbb{R}$ with $e^{t X_0}$
integrable; write $M(t) = \mathbb{E}[e^{t X_0}]$. Let $n > 0$ and let $E \subseteq \Omega$ be any
set on which the empirical mean satisfies

$$a \le t \cdot \frac{1}{n} \sum_{i < n} X_i - \log M(t) .$$

Then $\mu(E) \le e^{-na}$ ($\mu(E)$ the outer measure if $E$ is not measurable).

This is the one-dimensional core of the Cramér upper bound. The proof splits on the sign of $t$:
for $t > 0$ it applies the upper-tail Chernoff bound to the sum $S_n$, for $t < 0$ the lower-tail
Chernoff bound; in both cases the exponential moment of the sum factors as $M(t)^n$ by
independence and identical distribution.
