# Cramér's theorem in ℝᵈ

Let $X_0, X_1, \dots$ be independent, identically distributed random vectors in $\mathbb{R}^d$ with
$E[e^{\langle t, X_0 \rangle}] < \infty$ for every $t \in \mathbb{R}^d$. Then the laws of the empirical
means $\frac1n \sum_{i<n} X_i$ satisfy the large deviation principle with the good rate function

$$\Lambda^*(x) = \sup_{t} \bigl( \langle t, x \rangle - \log E[e^{\langle t, X_0 \rangle}] \bigr).$$

The proof combines the [upper bound for closed sets](limsup-log-empirical-mean-measure-vec-le.md),
the [lower bound for open sets](cramer-lower-bound.md) and the
[goodness of the rate function](is-good-rate-function-cramer-rate-functi.md).

In dimension one Varadhan proves the theorem directly: the Chebyshev bound
$P[\bar X_n \ge \ell] \le e^{-n(\theta \ell - \psi(\theta))}$ gives the upper bound for half-lines, and
exponential tilting $d\mu_{\theta_0}/d\mu = e^{\theta_0 x} / M(\theta_0)$, which makes $\ell$ the mean,
gives the lower bound. The proof here follows the same plan in $\mathbb{R}^d$: half-space Chernoff
bounds and exponential tightness above; below, the tilt is applied at points $x = \nabla\Lambda(\theta)$,
and a general $x$ with $\Lambda^*(x) < \infty$ is reached by maximising
$\langle x, t \rangle - \Lambda(t) - \varepsilon |t|^2/2$, whose maximiser $\theta_\varepsilon$ satisfies
$\nabla\Lambda(\theta_\varepsilon) = x - \varepsilon\theta_\varepsilon \to x$; the log-moment generating function is
differentiable by differentiation under the integral sign.

Varadhan also obtains the theorem in a separable Banach space as a corollary of Sanov's theorem:
the mean is a continuous function of the empirical measure on measures with bounded support, the
general case follows by truncation, and the contracted rate
$\inf \{ \int b \log b \, d\alpha : \int z \, b(z) \, d\alpha(z) = x \}$ equals $\Lambda^*(x)$ by a minimax
argument (Section 3, Corollary 1.3 and Lemma 1.4 of the notes).

## Sources

- S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University, Spring 2010, Section 1 (https://math.nyu.edu/~varadhan/LDP/1-2.pdf) and Section 3, Corollary 1.3 in the notes' numbering (https://math.nyu.edu/~varadhan/LDP/Spring2010.3.pdf).
- A. Dembo and O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed., Section 2.2.
