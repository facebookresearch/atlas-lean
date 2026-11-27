# Learnability by ridge regression

Let $E$ be a real inner product space and let examples $z$ carry features $\phi(z) \in E$ with $\|\phi(z)\| \le 1$ and labels $y(z) \in [-1, 1]$. Let $\ell(w, z) = \frac12(\langle w, \phi(z)\rangle - y(z))^2$ be the squared loss and $A$ a ridge regression rule, minimizing $L_S(w) + r\|w\|^2$ over all of $E$. For $\varepsilon \in (0,1)$, $B > 0$, $r = \varepsilon/(3B^2)$ and $m \ge 150B^2/\varepsilon^2$ i.i.d. examples from any distribution $D$ (with integrable losses of the outputs),

$$
\mathbb{E}_{S}\big[L_D(A(S))\big] \le L_D(w) + \varepsilon \quad \text{for every } w \text{ with } \|w\| \le B.
$$

## Proof sketch

The squared loss is convex and nonnegative in $w$ with derivative $(\langle w, \phi\rangle - y)\langle \phi, \cdot\rangle$, which is $\|\phi\|^2 \le 1$-Lipschitz, and $\ell(0,z) = y^2/2 \le 1$. Apply the smooth-loss oracle inequality with $\beta = 1$ and $K = E$.

## Depends on

- [Ridge objective](../least-squares-ridge-and-lasso-regression/ridge.md)
- [Convex-Lipschitz-bounded and convex-smooth-bounded learning problems](../../pac-learning/learnability-of-convex-problems/convex-lipschitz-bounded-and-convex-smooth-bounded-learning.md)

## Proof depends on

- [Stability and oracle inequality of RLM for smooth nonnegative losses](smooth-loss-rlm-stability-and-oracle-inequality.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
