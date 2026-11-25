# Rate score in the log rate

Let $\iota$ be a finite set of $n$ observations, with counts $k_i \in \mathbb{N}$ and size factors
$s_i$. For real $a$ and $b$, the log-rate score is

$$\tilde S_b(a, b) = \sum_{i \in \iota} \Bigl(a - (a + k_i)\, \frac{b}{b + s_i}\Bigr),$$

with the convention $x / 0 = 0$. For $b > 0$ and positive size factors $s_i > 0$ it is $b$ times the
[rate score](rate-score-mul-self.md), so it has the sign of the rate score, and for $a > 0$ it is
the [derivative](has-deriv-at-log-marginal-lik-log-rate.md) of the log marginal likelihood in
$\log b$.
