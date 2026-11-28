# Stability and oracle inequality of Tikhonov-regularized loss minimization

Let $E$ be a real inner product space, $K \subseteq E$ convex, $\ell : E \times Z \to \mathbb{R}$ a loss, $D$ a probability distribution on $Z$, and $A$ a regularized loss minimization (RLM) rule: on every sample $S \in Z^m$, $A(S)$ minimizes $L_S(w) + \mathcal{R}(w)$ over $w \in K$, where $L_S$ is the empirical risk. Write $S^{(i)}$ for $S$ with its $i$-th example replaced by a fresh $z'$, and assume the losses of the rule's outputs are integrable.
Take $\mathcal{R}(w) = r\|w\|^2$ with $r > 0$, and let every loss be convex and $\rho$-Lipschitz on $K$. Then $A$ is on-average replace-one stable with rate $2\rho^2/(rm)$ (Shalev-Shwartz and Ben-David, Corollary 13.6), and for $m > 0$ i.i.d. examples and every $w \in K$ with integrable loss,

$$
\mathbb{E}_{S \sim D^m}\big[L_D(A(S))\big] \le L_D(w) + r\|w\|^2 + \frac{2\rho^2}{rm}
$$

(Corollary 13.8). If $\rho > 0$, $B > 0$ and $r = \sqrt{2\rho^2/(B^2 m)}$, then $\mathbb{E}_S[L_D(A(S))] \le L_D(w) + \rho B\sqrt{8/m}$ for every $w \in K$ with $\|w\| \le B$ (Corollary 13.9).

## Proof sketch

Strong convexity of the regularized objective gives $\|A(S^{(i)}) - A(S)\| \le 2\rho/(rm)$, hence $\ell(A(S^{(i)}), z_i) - \ell(A(S), z_i) \le \rho\|A(S^{(i)}) - A(S)\| \le 2\rho^2/(rm)$ (Section 13.3.1). The expected generalization gap equals the replace-one gap, and the expected empirical risk of $A(S)$ is at most $L_D(w) + r\|w\|^2$ since $A(S)$ minimizes the regularized objective (Section 13.4). Optimize $r$ for the last statement.

Derived (not stated in the cited source): the two-sided growth inequality, with strong convexity modulus $2r$, gives $\|A(S^{(i)}) - A(S)\| \le \rho/(rm)$, so $A$ is on-average replace-one stable with the smaller rate $\rho^2/(rm)$.

## Depends on

- [Stability of regularized loss minimization](../../generalization-bounds-and-concentration/stability-of-regularized-loss-minimization.md)
- [Expected generalization gap equals replace-one stability term](../../generalization-bounds-and-concentration/algorithmic-stability/expected-generalization-gap-equals-replace-one-stability-ter.md)
- [Convex-Lipschitz-bounded and convex-smooth-bounded learning problems](../../pac-learning/learnability-of-convex-problems/convex-lipschitz-bounded-and-convex-smooth-bounded-learning.md)

## Proof depends on

- [Uniform stability of RLM with a strongly convex regularizer](strongly-convex-rlm-uniform-stability.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014, Section 13.3.1 and Corollaries 13.6, 13.8 and 13.9.
- O. Bousquet and A. Elisseeff, "Stability and Generalization", Journal of Machine Learning Research, 2002.
