# The gradient update of a Lipschitz function is $\alpha L$-bounded

Let $f$ be $L$-Lipschitz on a real Hilbert space and let $\alpha \ge 0$. Then the gradient update $G(w) = w - \alpha \nabla f(w)$ moves every point by at most $\alpha L$:

$$
\lVert w - G(w) \rVert = \lVert \alpha \nabla f(w) \rVert \le \alpha L .
$$

Proof: the derivative of an $L$-Lipschitz function has operator norm at most $L$, and the gradient has the norm of the derivative. (Where $f$ is not differentiable, the gradient is $0$ by convention.)

## Sources

- M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Lemma 3.3.
