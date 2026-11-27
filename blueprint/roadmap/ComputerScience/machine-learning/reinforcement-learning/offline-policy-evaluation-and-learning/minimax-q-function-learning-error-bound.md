# Error bound for minimax Q-function learning

If the data cover the target occupancy and the state-action density ratio lies in the convex hull of the discriminator class, the off-policy estimate $R_{\mathrm q}[q]$ of any candidate $q$ is off by at most $\sup_{g}|L_{\mathrm q}(q,g)|$, and minimax Q-function learning achieves the smallest such guarantee over its class.

Use the setting and notation of [minimax Q-function learning](minimax-q-function-learning.md): finite $\mathcal X=S\times A$, discount $\gamma\in[0,1)$, target policy $\pi_e$, data distribution $d_{\pi_b}$, loss $L_{\mathrm q}$, value estimate $R_{\mathrm q}[q]=(1-\gamma)\mathbb E_{s\sim d_0}[q(s,\pi_e)]$, population estimator $\hat q$, a minimizer of $\Psi(q)=\sup_{g\in\mathcal G}L_{\mathrm q}(q,g)^2$ over $\mathcal Q$, and the normalized return $R_{\pi_e}$. Let $w_{\pi_e/\pi_b}$ be the [discounted state-action density ratio](discounted-state-action-density-ratio.md), and assume the coverage condition $d_{\pi_e,\gamma}(s,a)\le C_w\,d_{\pi_b}(s,a)$ for all $(s,a)$ and some $C_w<\infty$ (their Assumption 2). Let $\operatorname{conv}(\mathcal G)$ be the set of finite convex combinations of elements of $\mathcal G$. Suprema are extended reals and may be $+\infty$; the source writes them as maxima and does not discuss attainment.

**Theorem (Uehara, Huang and Jiang, Theorem 5).** If $w_{\pi_e/\pi_b}\in\operatorname{conv}(\mathcal G)$, then for every $q:\mathcal X\to\mathbb R$

$$
\big|R_{\pi_e}-R_{\mathrm q}[q]\big|\le\sup_{g\in\mathcal G}\big|L_{\mathrm q}(q,g)\big|,
$$

and, when $\hat q$ is defined (the infimum of $\Psi$ over $\mathcal Q$ is attained and finite),

$$
\big|R_{\pi_e}-R_{\mathrm q}[\hat q]\big|\le\min_{q\in\mathcal Q}\sup_{g\in\mathcal G}\big|L_{\mathrm q}(q,g)\big|,
$$

the minimum being attained at $\hat q$. When the source's maxima exist these are its bounds; the theorem says nothing about $\hat q$ when it is undefined.

Realizability of $\mathcal Q$ makes the right side of the second bound $0$ but is not needed: with $\mathcal G=\{w_{\pi_e/\pi_b}\}$ a constant $q$ suffices (their Example 3). A combined estimator $R[w,q]=R_{\mathrm q}[q]+\mathbb E_{d_{\pi_b}}[w(s,a)(r+\gamma q(s',\pi_e)-q(s,a))]$ is exact when either $w=w_{\pi_e/\pi_b}$ or $q=Q^{\pi_e}$, and satisfies both this bound and the one for [minimax weight learning](minimax-weight-learning-error-bound.md) under shifted hypotheses (their Lemma 7 and Theorem 8).

## Depends on

- [Minimax Q-function learning](minimax-q-function-learning.md)
- [Discounted state-action density ratio](discounted-state-action-density-ratio.md)

## Proof depends on

- [Occupancy averages](../stochastic-policies-and-discounted-occupancy/sum-visitation-mul.md)

## Expansion

By the coverage condition, $\mathbb E_{d_{\pi_b}}[w_{\pi_e/\pi_b}\,h]=\mathbb E_{d_{\pi_e,\gamma}}[h]$ for every function $h$ of a data tuple, so for every $q$, $L_{\mathrm q}(q,w_{\pi_e/\pi_b})=\mathbb E_{d_{\pi_e,\gamma}}[r+\gamma q(s',\pi_e)-q(s,a)]$. Using $\mathbb E_{d_{\pi_e,\gamma}}[r]=R_{\pi_e}$ and the flow identity $\mathbb E_{d_{\pi_e,\gamma}}[\gamma q(s',\pi_e)]=\mathbb E_{d_{\pi_e,\gamma}}[q(s,a)]-(1-\gamma)\mathbb E_{d_0}[q(s,\pi_e)]$, this equals $R_{\pi_e}-R_{\mathrm q}[q]$. The loss is linear in $g$, so its absolute value at a convex combination of discriminators is at most $\sup_{g\in\mathcal G}|L_{\mathrm q}(q,g)|$, and the second bound follows because $\hat q$ minimizes $\Psi$, hence $\Psi^{1/2}$.

## Sources

- M. Uehara, J. Huang and N. Jiang, *Minimax Weight and Q-Function Learning for Off-Policy Evaluation*, Proceedings of the 37th International Conference on Machine Learning, PMLR 119:9659–9668 (2020). [arXiv:1910.12809v4](https://arxiv.org/abs/1910.12809v4), §5, Theorem 5 and Example 3; §6, Lemma 7 and Theorem 8; proofs in Appendices B and C.
