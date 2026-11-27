# Uniqueness of the IPO minimizer

When the behavior policy and the reference policy have the same support, the IPO root-finding loss has exactly one local minimum among policies with that support; it is the global minimum, attained at the maximizer of the IPO objective.

Fix a context and suppress it from the notation. Let $Y$ be finite, $\tau > 0$, let $\mu$ and $\pi_{\mathrm{ref}}$ be distributions on $Y$ with $\mathrm{Supp}(\mu) = \mathrm{Supp}(\pi_{\mathrm{ref}}) = J$, and let $\Pi$ be the set of policies $\pi$ with $\mathrm{Supp}(\pi) = J$. Let $L$ be the [IPO root-finding loss](identity-preference-optimization-loss.md) and

$$\pi^*(y) = \frac{\pi_{\mathrm{ref}}(y)\, e^{p^*(y \succ \mu)/\tau}}{\sum_{y'} \pi_{\mathrm{ref}}(y')\, e^{p^*(y' \succ \mu)/\tau}},$$

the maximizer of the [IPO objective](psi-preference-optimization.md). Then $\pi^* \in \Pi$, $L(\pi^*) = 0$, and $\pi \mapsto L(\pi)$ has a unique local minimum in $\Pi$, which is its unique global minimum $\pi^*$.

## Depends on

- [Identity preference optimization loss](identity-preference-optimization-loss.md)
- [Ψ-preference optimization](psi-preference-optimization.md)
- [Optimal policy of KL-regularized reward maximization](optimal-policy-of-kl-regularized-rewards.md)

## Proof depends on

- [Optimal policy of KL-regularized reward maximization](optimal-policy-of-kl-regularized-rewards.md)
- [Stationary points of convex functions are global minimizers](../../../../../Analysis/convex-analysis-and-variations/first-order-conditions-for-convexity/is-min-on-of-has-fderiv-at-eq-zero.md)
- [Strict convexity of a positive-definite quadratic form](../../../../../LinearAlgebra/positive-definite-matrices/strict-convexity-of-positive-definite-quadratic.md)

## Expansion

$L \ge 0$ as an expectation of squares, and $L(\pi^*) = 0$ because $h_{\pi^*}(y, y') = \tau^{-1}(p^*(y \succ \mu) - p^*(y' \succ \mu))$ on $J$. Parameterize $\Pi$ by logits $s \in \mathbb{R}^J$, $\pi_s(y) = e^{s(y)}/\sum_{y' \in J} e^{s(y')}$; then $h_{\pi_s}(y,y') = s(y) - s(y') + \log(\pi_{\mathrm{ref}}(y')/\pi_{\mathrm{ref}}(y))$, so $F(s) = L(\pi_s)$ is a quadratic polynomial in $s$ whose quadratic part is $\sum_{y, y' \in J} \mu(y)\mu(y')(s(y) - s(y'))^2 = s^{\mathsf T} M s$ with $M$ positive semidefinite. Because $\mu > 0$ on $J$, $s^{\mathsf T} M s = 0$ exactly when $s$ is constant on $J$, so $\ker M$ is the line spanned by $(1, \dots, 1)$, and moving along that line leaves $\pi_s$ unchanged. The proof then runs as follows. (i) If $\pi = \pi_{s_0}$ is a local minimizer of $L$ on $\Pi$, then $s_0$ is a local minimizer of $F$ on $\mathbb{R}^J$, since $s \mapsto \pi_s$ is continuous; as $F$ is differentiable, $DF(s_0) = 0$. (ii) $F$ is convex, so a stationary point is a global minimizer. (iii) The minimizers of the quadratic $F$ with positive semidefinite, singular $M$ form an affine set $\{s : Ms = b\}$, a single coset $s_* + \mathbb{R}(1, \dots, 1)$ of $\ker M$, and all its points give the same policy, which is $\pi^*$ since $L(\pi^*) = 0$ is the minimum value. Step (i) uses that the derivative of a differentiable function vanishes at an interior local minimum; the source invokes instead that local minimizers of a convex function are global (Boyd and Vandenberghe, Chapter 4), and no statement page for either fact is linked here.

Without the support condition uniqueness fails: if $\pi$ may charge responses outside the support of $\mu$, the loss does not constrain those probabilities. In the source's example with three actions, uniform $\pi_{\mathrm{ref}}$ and $\mu$ uniform on two of them, every policy whose ratio of the first two probabilities is $e^{(p^*(y_1 \succ \mu) - p^*(y_2 \succ \mu))/\tau}$ is a global minimizer.

## Sources

- M. Gheshlaghi Azar, M. Rowland, B. Piot, D. Guo, D. Calandriello, M. Valko and R. Munos, *A General Theoretical Paradigm to Understand Learning from Human Preferences*, Proceedings of the 27th International Conference on Artificial Intelligence and Statistics (AISTATS 2024), PMLR 238, Theorem 2 and its proof (Section 5.1, equations (14) and (15)), and Appendix A.2 (non-uniqueness when the supports differ). [publisher page](https://proceedings.mlr.press/v238/gheshlaghi-azar24a.html)
