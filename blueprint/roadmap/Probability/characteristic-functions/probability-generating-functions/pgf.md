# Probability generating function

For a measure $\mu$ on $\Omega$ and a function
$X : \Omega \to \mathbb{N}$, the probability generating function of $X$ under $\mu$ is the function
$G_X : \mathbb{R} \to \mathbb{R}$ given by

$$G_X(s) = \int_\Omega s^{X(\omega)} \, d\mu(\omega),$$

which is the expectation $\mathbb{E}[s^X]$ when $\mu$ is a probability measure.

For a finite measure $\mu$ and measurable $X$ the integral converges whenever $|s| \le 1$. Where
$s^X$ is not integrable, the integral is taken to be $0$.
