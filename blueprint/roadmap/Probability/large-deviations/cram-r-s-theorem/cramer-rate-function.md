# Cramér rate function

For a random vector $X$ in $\mathbb{R}^d$ under a measure $\mu$, the Cramér rate function is the
Legendre transform of the logarithmic moment generating function,

$$\Lambda^*(x) = \sup_{t \in \mathbb{R}^d} \bigl( \langle t, x \rangle - \log E[e^{\langle t, X \rangle}] \bigr),$$

stored in $[0, \infty]$, a negative supremum being read as $0$, where
$\log E[e^{\langle t, X\rangle}] = \infty$ at directions with infinite exponential moment (such
directions contribute nothing to the supremum). Under a probability measure the direction $t = 0$
contributes $0$, so the supremum is nonnegative and storing it in $[0, \infty]$ loses nothing. It
is convex and lower semicontinuous, vanishes at the mean when the moment generating function is
finite, and, under a probability measure, is the rate function of Cramér's theorem for the
empirical mean. The definition makes sense for every measure, but for a measure that is not a
probability measure it is only a truncated conjugate, not the Cramér rate: under the zero measure
it is $\infty$ everywhere, and for total mass $c \ne 1$ the supremum is shifted by $-\log c$
before negative values are read as $0$.

In Varadhan's notes the rate function appears in dimension one as
$h(\ell) = \sup_\theta [\theta \ell - \psi(\theta)]$ with $\psi = \log M$, equation (1.3), right after the
Chebyshev bound $\frac1n \log P[\bar X_n \ge \ell] \le -\sup_{\theta \ge 0} [\theta \ell - \psi(\theta)]$.

## Sources

- S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University, Spring 2010, Section 1, equation (1.3) (https://math.nyu.edu/~varadhan/LDP/1-2.pdf).
