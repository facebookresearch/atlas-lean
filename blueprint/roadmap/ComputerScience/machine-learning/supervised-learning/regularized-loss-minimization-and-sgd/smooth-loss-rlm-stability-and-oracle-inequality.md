# Stability and oracle inequality of RLM for smooth nonnegative losses

Let $E$ be a real inner product space, $K \subseteq E$ convex, $\ell : E \times Z \to \mathbb{R}$ a loss, $D$ a probability distribution on $Z$, and $A$ a regularized loss minimization (RLM) rule: on every sample $S \in Z^m$, $A(S)$ minimizes $L_S(w) + \mathcal{R}(w)$ over $w \in K$, where $L_S$ is the empirical risk. Write $S^{(i)}$ for $S$ with its $i$-th example replaced by a fresh $z'$, and assume the losses of the rule's outputs are integrable.
Let every loss be convex on $K$, nonnegative, and differentiable on $E$ with $\beta$-Lipschitz derivative. If $\mathcal{R}$ is $\sigma$-strongly convex on $K$ with $\sigma > 0$ and $4\beta \le \sigma m$, the expected replace-one gap is at most $\frac{10\beta}{\sigma m}\mathbb{E}_S[L_S(A(S))]$. For Tikhonov regularization $r\|w\|^2$ with $2\beta \le rm$ the factor is $5\beta/(rm)$, and for every $w \in K$ with integrable loss

$$
\mathbb{E}_S\big[L_D(A(S))\big] \le \Big(1 + \frac{5\beta}{rm}\Big)\mathbb{E}_S\big[L_S(A(S))\big] \le \Big(1 + \frac{5\beta}{rm}\Big)\big(L_D(w) + r\|w\|^2\big).
$$

If moreover $0 \in K$, $\ell(0, z) \le 1$ for all $z$, $\varepsilon \in (0,1)$, $B > 0$, $m \ge 150\beta B^2/\varepsilon^2$ and $r = \varepsilon/(3B^2)$, then $\mathbb{E}_S[L_D(A(S))] \le L_D(w) + \varepsilon$ for every $w \in K$ with $\|w\| \le B$.

## Proof sketch

For nonnegative $\beta$-smooth losses, $\|\nabla \ell(w,z)\|^2 \le 2\beta\,\ell(w,z)$ (self-bounding). Combined with the two-sided growth inequality this yields $\sigma m(\ell(A(S^{(i)}), z_i) - \ell(A(S), z_i)) \le 5\beta(\ell(A(S), z_i) + \ell(A(S^{(i)}), z'))$ when $4\beta \le \sigma m$, a positive-definite quadratic estimate. Taking expectations, both terms average to the expected empirical risk; the oracle inequality and the parameter choice follow as in the Lipschitz case.

## Depends on

- [Stability of regularized loss minimization](../../generalization-bounds-and-concentration/stability-of-regularized-loss-minimization.md)
- [Expected generalization gap equals replace-one stability term](../../generalization-bounds-and-concentration/algorithmic-stability/expected-generalization-gap-equals-replace-one-stability-ter.md)
- [Convex-Lipschitz-bounded and convex-smooth-bounded learning problems](../../pac-learning/learnability-of-convex-problems/convex-lipschitz-bounded-and-convex-smooth-bounded-learning.md)

## Proof depends on

- [Uniform stability of RLM with a strongly convex regularizer](strongly-convex-rlm-uniform-stability.md)
- [Expected generalization gap equals replace-one stability term](../../generalization-bounds-and-concentration/algorithmic-stability/expected-generalization-gap-equals-replace-one-stability-ter.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
