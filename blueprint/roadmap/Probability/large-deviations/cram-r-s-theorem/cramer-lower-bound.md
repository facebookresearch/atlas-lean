# Cramér lower bound for open sets

Let $X_0, X_1, \dots$ be independent, identically distributed random vectors in $\mathbb{R}^d$ with
$E[e^{\langle t, X_0 \rangle}] < \infty$ for every $t$, and let $\mu_n$ be the law of the empirical
mean. For every open set $U \subseteq \mathbb{R}^d$,

$$-\inf_{x \in U} \Lambda^*(x) \le \liminf_{n \to \infty} \frac{1}{n} \log \mu_n(U),$$

in exactly the form required by the large deviation principle.

At a point $x = \nabla\Lambda(\theta)$ the weight $e^{\langle \theta, S_n \rangle - n\Lambda(\theta)}$ tilts the
sample so that $x$ becomes the mean, and on the ball $B(x, \delta)$ it is at most
$e^{n(\langle\theta, x\rangle - \Lambda(\theta)) + n|\theta|\delta}$; the tilted mass of the complement of the ball
is exponentially small by Chernoff bounds in the $2d$ coordinate half-spaces, which gives
$\liminf \frac1n \log \mu_n(B(x,\delta)) \ge -(\langle\theta, x\rangle - \Lambda(\theta)) - |\theta|\delta$. A general point is
reached through the maximiser of $\langle x, t\rangle - \Lambda(t) - \varepsilon|t|^2/2$.

## Sources

- S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University, Spring 2010, Section 1 (exponential tilting in dimension one) (https://math.nyu.edu/~varadhan/LDP/1-2.pdf); A. Dembo and O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed., Section 2.2.
