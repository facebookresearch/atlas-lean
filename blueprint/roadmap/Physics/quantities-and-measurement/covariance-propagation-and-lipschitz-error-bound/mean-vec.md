# Weighted mean vector of $X$ on a finite sample space

Let $\Omega$ be a finite set, $p : \Omega \to \mathbb{R}$ real weights and
$X : \Omega \to \mathbb{R}^n$ a random vector with coordinates $X_1, \dots, X_n$. Its weighted mean
vector is the vector $\bar X \in \mathbb{R}^n$ with coordinates

$$\bar X_i = \sum_{\omega \in \Omega} p(\omega)\, X_i(\omega), \qquad i = 1, \dots, n .$$

No condition is imposed on the weights, and for an empty $\Omega$ the sum is the zero vector. When
$p$ is a probability distribution on $\Omega$ (weights $p(\omega) \ge 0$ with
$\sum_\omega p(\omega) = 1$), $\bar X$ is the mean vector of $X$; on a finite sample space every
moment is finite, so no integrability condition arises. For other weights $\bar X$ is only this
weighted sum.
