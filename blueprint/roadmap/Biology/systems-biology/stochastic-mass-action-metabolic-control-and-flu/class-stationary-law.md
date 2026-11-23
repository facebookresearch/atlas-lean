# Normalized Poisson stationary law on a finite state class

Let $S$ be a finite set, $c \in \mathbb{R}^S$ and $\Omega \subseteq \mathbb{N}^S$ a finite set of states.
The normalized Poisson law on $\Omega$ is

$$\pi_\Omega(x) = \frac{\pi(x)}{\sum_{y \in \Omega} \pi(y)} \qquad (x \in \Omega),$$

where $\pi(x) = \prod_s c_s^{x_s} e^{-c_s}/x_s!$ are the [Poisson weights](poisson-weight.md), with the
quotient read as $0$ when the denominator vanishes.
