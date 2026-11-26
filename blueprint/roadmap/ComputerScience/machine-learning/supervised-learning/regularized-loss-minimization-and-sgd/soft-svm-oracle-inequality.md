# Oracle inequality for Soft-SVM

Let $E$ be a real inner product space and let examples $z$ carry features $\phi(z)$ with $\|\phi(z)\| \le \rho$ and labels $y(z)$ with $|y(z)| \le 1$. The hinge loss $\ell(w, z) = \max(0, 1 - y(z)\langle w, \phi(z)\rangle)$ is convex in $w$ and $|y(z)|\,\|\phi(z)\|$-Lipschitz. Let $A$ minimize the empirical hinge risk plus $r\|w\|^2$, $r > 0$, over $E$ (Soft-SVM). For $m > 0$ i.i.d. examples and every $u \in E$,

$$
\mathbb{E}_S\big[L_D(A(S))\big] \le L_D(u) + r\|u\|^2 + \frac{2\rho^2}{rm},
$$

where $L_D$ is the true hinge risk.

## Proof sketch

Convexity and the Lipschitz bound of the hinge loss follow from those of $t \mapsto \max(0, 1-t)$ composed with the linear map $w \mapsto y\langle w, \phi\rangle$. Apply the Tikhonov RLM oracle inequality with $K = E$ and Lipschitz constant $\rho$.

## Depends on

- [Soft-margin support vector machine objective](../logistic-regression-and-support-vector-machines/svm-objective.md)
- [Stability and oracle inequality of Tikhonov-regularized loss minimization](tikhonov-rlm-stability-and-oracle-inequality.md)

## Proof depends on

- [Stability and oracle inequality of Tikhonov-regularized loss minimization](tikhonov-rlm-stability-and-oracle-inequality.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
