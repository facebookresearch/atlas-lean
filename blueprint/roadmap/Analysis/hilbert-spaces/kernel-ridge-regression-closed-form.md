# Kernel ridge regression closed form

Let $K$ be a positive semidefinite kernel with feature space $\mathcal{H}$, let $(x_i, y_i)_{i=1}^m$ be data and
$\lambda > 0$, and minimize $\frac1m \sum_{i=1}^m (\langle w, \psi(x_i) \rangle - y_i)^2 + \lambda \lVert w \rVert^2$ over
$w \in \mathcal{H}$. The minimizer is $w = \sum_i \alpha_i \psi(x_i)$ with $\alpha = (G + \lambda m I)^{-1} y$, $G$ the Gram
matrix, so predictions are $f(x) = \sum_i \alpha_i K(x_i, x)$. With the sum-of-squares objective
$\sum_i (\cdot)^2 + \lambda \lVert w \rVert^2$ instead, $\lambda m$ becomes $\lambda$. This coefficient vector is the one in the posterior mean $f(x) = \sum_i \alpha_i K(x_i, x)$, $\alpha = (G + \sigma^2 I)^{-1} y$, of
a zero-mean Gaussian process with covariance $K$ observed with independent Gaussian noise of variance
$\sigma^2 = \lambda m$.

## Expansion

This node states a precise result.

## Proof depends on

- [Representer theorem](representer-theorem/mem-span-of-is-min-on.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Equations (13.3)–(13.5) (ridge regression; their objective carries a factor $\tfrac12$ on the squared loss, giving $2\lambda m$ in place of $\lambda m$) and Theorem 16.1 (representer theorem); the closed form follows by substituting $w = \sum_i \alpha_i \psi(x_i)$ and solving the resulting linear system. <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
- C. E. Rasmussen and C. K. I. Williams, *Gaussian Processes for Machine Learning*, MIT Press, 2006, Section 2.2: the posterior mean $\bar f_* = k_*^{\mathsf T}(K + \sigma_n^2 I)^{-1}y$, Eq. (2.25), and its kernel expansion $\sum_i \alpha_i k(x_i, x_*)$ with $\alpha = (K + \sigma_n^2 I)^{-1}y$, Eq. (2.27). <http://gaussianprocess.org/gpml/chapters/RW2.pdf>
