# Error bound for minimax weight learning

If the target policy's action-value function lies in the convex hull of the discriminator class, the off-policy estimate given by any weight function $w$ is off by at most $\sup_{f}|L_{\mathrm w}(w,f)|$, and the population minimax estimator achieves the smallest such guarantee over the weight class.

Use the setting and notation of [minimax weight learning](minimax-weight-learning.md): finite $\mathcal X=S\times A$, discount $\gamma\in[0,1)$, target policy $\pi_e$, data distribution $d_{\pi_b}$, loss $L_{\mathrm w}$, value estimate $R_{\mathrm w}[w]=\mathbb E_{d_{\pi_b}}[w(s,a)\,r]$ and population estimator $\hat w$, a minimizer of $\Phi(w)=\sup_{f\in\mathcal F}L_{\mathrm w}(w,f)^2$ over $\mathcal W$. Let $Q^{\pi_e}$ be the action value of $\pi_e$ (unnormalized, $Q^{\pi_e}(s,a)=\mathbb E[\sum_{t\ge0}\gamma^t r_t\mid s_0=s,a_0=a]$ with later actions from $\pi_e$), and $R_{\pi_e}$ its normalized return. Let $\operatorname{conv}(\mathcal F)$ be the set of finite convex combinations of elements of $\mathcal F$. Suprema are extended reals and may be $+\infty$; the source writes them as maxima and does not discuss attainment.

**Theorem (Uehara, Huang and Jiang, Theorem 2).** If $Q^{\pi_e}\in\operatorname{conv}(\mathcal F)$, then for every $w:\mathcal X\to\mathbb R$

$$
\big|R_{\pi_e}-R_{\mathrm w}[w]\big|\le\sup_{f\in\mathcal F}\big|L_{\mathrm w}(w,f)\big|,
$$

and, when $\hat w$ is defined (the infimum of $\Phi$ over $\mathcal W$ is attained and finite),

$$
\big|R_{\pi_e}-R_{\mathrm w}[\hat w]\big|\le\min_{w\in\mathcal W}\sup_{f\in\mathcal F}\big|L_{\mathrm w}(w,f)\big|,
$$

the minimum being attained at $\hat w$. When the source's maxima exist these are its bounds; the theorem says nothing about $\hat w$ when it is undefined.

The theorem needs no realizability of the weight class: under the coverage condition $d_{\pi_e,\gamma}(s,a)\le C_w\,d_{\pi_b}(s,a)$ of the [discounted state-action density ratio](discounted-state-action-density-ratio.md), if $w_{\pi_e/\pi_b}\in\mathcal W$ the right side of the second bound is $0$, but it can also vanish otherwise (their Example 1, where $\mathcal F=\{Q^{\pi_e}\}$ and $\mathcal W$ contains a suitable constant). The condition on $\mathcal F$ is what the guarantee rests on, and adding functions to $\mathcal F$ never breaks it. Finite-sample versions, which add a Rademacher-complexity term for the empirical loss, are their Theorem 9.

## Depends on

- [Minimax weight learning](minimax-weight-learning.md)
- [Action value of a stochastic policy](../performance-difference-lemma/stoch-qvalue.md)

## Proof depends on

- [Bellman consistency for stochastic policies](../stochastic-policies-and-discounted-occupancy/stoch-value-eq.md)

## Expansion

Substituting $f=Q^{\pi_e}$ and using the Bellman equation $\mathbb E[r\mid s,a]=Q^{\pi_e}(s,a)-\gamma\,\mathbb E[Q^{\pi_e}(s',\pi_e)\mid s,a]$ gives $L_{\mathrm w}(w,Q^{\pi_e})=R_{\pi_e}-R_{\mathrm w}[w]$ for every $w$. Since $L_{\mathrm w}(w,\cdot)$ is linear in $f$ and convex weights sum to one, $|L_{\mathrm w}(w,\sum_i\lambda_if_i)|\le\sum_i\lambda_i|L_{\mathrm w}(w,f_i)|\le\sup_{f\in\mathcal F}|L_{\mathrm w}(w,f)|$. The second bound follows because $\hat w$ minimizes $\Phi$, hence $\sup_f|L_{\mathrm w}(w,f)|=\Phi(w)^{1/2}$, over $\mathcal W$.

## Sources

- M. Uehara, J. Huang and N. Jiang, *Minimax Weight and Q-Function Learning for Off-Policy Evaluation*, Proceedings of the 37th International Conference on Machine Learning, PMLR 119:9659–9668 (2020). [arXiv:1910.12809v4](https://arxiv.org/abs/1910.12809v4), §4, Theorem 2 and Example 1; §6, Theorem 9; proof of Theorem 2 in Appendix A.
