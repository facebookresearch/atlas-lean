# Cramér lower bound for open sets, assuming a differentiable log moment generating function

Let $X_0, X_1, \dots$ be independent, identically distributed random vectors in $\mathbb{R}^d$ with
$E[e^{\langle t, X_0 \rangle}] < \infty$ for every $t$, and suppose that
$\Lambda(t) = \log E[e^{\langle t, X_0 \rangle}]$ is differentiable. Then for every open set $U$,

$$-\inf_{x \in U} \Lambda^*(x) \le \liminf_{n \to \infty} \frac{1}{n} \log \mu_n(U).$$

The differentiability hypothesis always holds under finite exponential moments
([differentiability of the log moment generating function](differentiable-log-mgfvec.md)); this
is the step of the proof of the [lower bound](cramer-lower-bound.md) that reduces a general point
to gradient points. For $x \in U$ with $\Lambda^*(x) < \infty$ and $\varepsilon > 0$, a maximiser
$\theta$ of $t \mapsto \langle x, t \rangle - \Lambda(t) - \varepsilon |t|^2 / 2$ satisfies
$\nabla\Lambda(\theta) = x - \varepsilon\theta$, with $\varepsilon |\theta| \to 0$ and
$\langle \theta, x - \varepsilon\theta \rangle - \Lambda(\theta) \le \Lambda^*(x)$; the
[ball bound at gradient points](cramer-lower-bound-ball.md) at $x - \varepsilon\theta$ concludes.

## Sources

- S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University, Spring 2010, Section 1 (https://math.nyu.edu/~varadhan/LDP/1-2.pdf); A. Dembo and O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed., Section 2.2.
