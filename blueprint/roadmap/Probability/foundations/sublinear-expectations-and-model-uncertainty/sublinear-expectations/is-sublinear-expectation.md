# Sublinear expectation

Let $\mathcal{H}$ be a linear space of real functions on a set $\Omega$. A functional
$\mathbb{E}$ on real functions on $\Omega$ is a sublinear expectation on $\mathcal{H}$ if
$\mathcal{H}$ contains the constants and, for all $X, Y \in \mathcal{H}$: $\mathbb{E}[Y] \le \mathbb{E}[X]$
whenever $Y \le X$ (monotonicity); $\mathbb{E}[c] = c$ for every constant $c$ (constant
preservation); $\mathbb{E}[X + Y] \le \mathbb{E}[X] + \mathbb{E}[Y]$ (subadditivity); and
$\mathbb{E}[cX] = c\, \mathbb{E}[X]$ for $c \ge 0$ (positive homogeneity). Only the values of
$\mathbb{E}$ on $\mathcal{H}$ are constrained. Peng also assumes $|X| \in \mathcal{H}$ for
$X \in \mathcal{H}$; this definition omits that condition.

## Sources

- S. Peng, *Nonlinear Expectations and Stochastic Calculus under Uncertainty*,
  arXiv:1002.4546v1, 2010, Chapter I, Definition 1.1.
