# Stability of regularized loss minimization

Consider a learning problem with hypotheses $w \in \mathbb{R}^d$ and a loss $\ell(w, z)$ that is convex and
$\rho$-Lipschitz in $w$ for every example $z$. For $\lambda > 0$ and a sample $S$ of $m \ge 1$ examples, let
$A(S) = \arg\min_w \big(L_S(w) + \lambda\|w\|^2\big)$, which exists and is unique because the objective is strongly
convex. Then $A$ is on-average-replace-one-stable with rate $2\rho^2/(\lambda m)$, and for every $w^*$,

$$\mathbb{E}_S[L_\mathcal{D}(A(S))] \le L_\mathcal{D}(w^*) + \lambda\|w^*\|^2 + \frac{2\rho^2}{\lambda m}.$$

In particular, if $\rho > 0$, $B > 0$, $\|w^*\| \le B$ and $\lambda = \frac{\rho}{B}\sqrt{2/m}$, then
$\mathbb{E}_S[L_\mathcal{D}(A(S))] \le L_\mathcal{D}(w^*) + \rho B\sqrt{8/m}$.

## Depends on

- [Convex-Lipschitz-bounded and convex-smooth-bounded learning problems](../pac-learning/learnability-of-convex-problems/convex-lipschitz-bounded-and-convex-smooth-bounded-learning.md)
- [On-average replace-one stability](algorithmic-stability/on-average-replace-one-stability.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Corollaries 13.6 and 13.8. <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
