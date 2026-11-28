# Coverage of a pivot confidence set

Let $(P_\theta)_{\theta \in \Theta}$ be probability measures on a measurable space $\mathcal X$, $\nu$ a probability measure on $\mathbb{R}$ with continuous distribution function $F_\nu(s) = \nu((-\infty, s])$ and quantile function $Q_\nu(u) = \inf\{s : u \le F_\nu(s)\}$ for $u \in (0,1)$ ($0$ otherwise), and $T : \mathcal X \times \Theta \to \mathbb{R}$ such that $x \mapsto T(x, \theta)$ is measurable and has law $\nu$ under $P_\theta$, for every $\theta$. Then for every $\alpha \in (0,1)$ and every $\theta$

$$P_\theta\big(Q_\nu(\alpha/2) \le T(x, \theta) \le Q_\nu(1 - \alpha/2)\big) \ge 1 - \alpha.$$
