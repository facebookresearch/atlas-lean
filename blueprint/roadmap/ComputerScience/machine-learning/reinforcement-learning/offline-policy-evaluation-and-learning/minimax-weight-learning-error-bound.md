# Error bound for minimax weight learning

If the target policy's action-value function lies in the convex hull of the discriminator class, the off-policy estimate given by any weight function $w$ is off by at most $\max_{f}|L_{\mathrm w}(w,f)|$, and minimax weight learning achieves the smallest such guarantee over the weight class.

Use the setting and notation of [minimax weight learning](minimax-weight-learning.md): finite $\mathcal X=S\times A$, discount $\gamma\in[0,1)$, target policy $\pi_e$, data distribution $d_{\pi_b}$, loss $L_{\mathrm w}$, value estimate $R_{\mathrm w}[w]=\mathbb E_{d_{\pi_b}}[w(s,a)\,r]$ and population estimator $\hat w$. Let $Q^{\pi_e}$ be the action value of $\pi_e$ (unnormalized, $Q^{\pi_e}(s,a)=\mathbb E[\sum_{t\ge0}\gamma^t r_t\mid s_0=s,a_0=a]$ with later actions from $\pi_e$), and $R_{\pi_e}$ its normalized return. Let $\operatorname{conv}(\mathcal F)$ be the set of finite convex combinations of elements of $\mathcal F$. Assume the maxima over $\mathcal F$ and the minimum over $\mathcal W$ below are attained.

**Theorem (Uehara, Huang and Jiang, Theorem 2).** If $Q^{\pi_e}\in\operatorname{conv}(\mathcal F)$, then for every $w:\mathcal X\to\mathbb R$

$$
\big|R_{\pi_e}-R_{\mathrm w}[w]\big|\le\max_{f\in\mathcal F}\big|L_{\mathrm w}(w,f)\big|,
$$

and

$$
\big|R_{\pi_e}-R_{\mathrm w}[\hat w]\big|\le\min_{w\in\mathcal W}\max_{f\in\mathcal F}\big|L_{\mathrm w}(w,f)\big|.
$$

The theorem needs no realizability of the weight class: if $w_{\pi_e/\pi_b}\in\mathcal W$ the right side of the second bound is $0$, but it can also vanish otherwise (their Example 1, where $\mathcal F=\{Q^{\pi_e}\}$ and $\mathcal W$ contains a suitable constant). The condition on $\mathcal F$ is what the guarantee rests on, and adding functions to $\mathcal F$ never breaks it. Finite-sample versions, which add a Rademacher-complexity term for the empirical loss, are their Theorem 9.

## Depends on

- [Minimax weight learning](minimax-weight-learning.md)
- [Action value of a stochastic policy](../performance-difference-lemma/stoch-qvalue.md)

## Proof depends on

- [Bellman consistency for stochastic policies](../stochastic-policies-and-discounted-occupancy/stoch-value-eq.md)

## Expansion

Substituting $f=Q^{\pi_e}$ and using the Bellman equation $\mathbb E[r\mid s,a]=Q^{\pi_e}(s,a)-\gamma\,\mathbb E[Q^{\pi_e}(s',\pi_e)\mid s,a]$ gives $L_{\mathrm w}(w,Q^{\pi_e})=R_{\pi_e}-R_{\mathrm w}[w]$ for every $w$. Since $L_{\mathrm w}(w,\cdot)$ is linear in $f$ and convex weights sum to one, $|L_{\mathrm w}(w,\sum_i\lambda_if_i)|\le\sum_i\lambda_i|L_{\mathrm w}(w,f_i)|\le\max_i|L_{\mathrm w}(w,f_i)|$. The second bound follows because $\hat w$ minimizes $\max_f L_{\mathrm w}(w,f)^2$, hence $\max_f|L_{\mathrm w}(w,f)|$, over $\mathcal W$.

## Sources

- M. Uehara, J. Huang and N. Jiang, *Minimax Weight and Q-Function Learning for Off-Policy Evaluation*, Proceedings of the 37th International Conference on Machine Learning, PMLR 119:9659–9668 (2020). [arXiv:1910.12809v4](https://arxiv.org/abs/1910.12809v4), §4, Theorem 2 and Example 1; §6, Theorem 9; proof of Theorem 2 in Appendix A.
