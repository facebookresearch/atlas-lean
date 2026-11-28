# Confidence set from a pivot

Let $T : \mathcal X \times \Theta \to \mathbb{R}$ be a pivot, $\nu$ a reference law on $\mathbb{R}$ with distribution function $F_\nu(s) = \nu((-\infty, s])$ and quantile function $Q_\nu(u) = \inf\{s : u \le F_\nu(s)\}$ for $u \in (0,1)$ ($0$ otherwise), and $\alpha \in \mathbb{R}$. The pivot confidence set at the observation $x$ is

$$C(x) = \big\{\theta \in \Theta : Q_\nu(\alpha/2) \le T(x, \theta) \le Q_\nu(1 - \alpha/2)\big\};$$

it need not be an interval.
