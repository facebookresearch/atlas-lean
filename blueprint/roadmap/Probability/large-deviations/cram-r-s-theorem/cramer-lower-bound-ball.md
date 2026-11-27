# Cramér lower bound on small balls at gradient points

Let $\mu$ be a probability measure and let $X_0, X_1, \dots$ be measurable, independent,
identically distributed random vectors in $\mathbb{R}^d$ with
$\mathbb{E}[e^{\langle t, X_0\rangle}] < \infty$ for every $t \in \mathbb{R}^d$. Let $\mu_n$ be
the [law of the empirical mean](empirical-mean-measure-vec.md) and
$\Lambda(t) = \log \mathbb{E}[e^{\langle t, X_0\rangle}]$, and suppose that $\Lambda$ is
differentiable at $\theta$ with gradient $x$. Then for every $\delta > 0$,

$$\liminf_{n \to \infty} \frac{1}{n} \log \mu_n(B(x, \delta)) \ge -\big(\langle \theta, x\rangle - \Lambda(\theta)\big) - \|\theta\|\, \delta ,$$

the $\liminf$ taken in $[-\infty, \infty]$.

The proof tilts by $\exp(\langle \theta, S_n\rangle - n \Lambda(\theta))$ inside the expectation
under the original law: the tilted mass of the complement of the ball is exponentially small by
the Chernoff bound in the $2d$ coordinate directions, using the derivative of $\Lambda$ at
$\theta$.

## Sources

- S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University, Spring 2010,
  Section 1 (tilting proof in $\mathbb{R}$), https://math.nyu.edu/~varadhan/LDP/1-2.pdf.
- A. Dembo and O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed.,
  Springer, 1998, Section 2.2.
