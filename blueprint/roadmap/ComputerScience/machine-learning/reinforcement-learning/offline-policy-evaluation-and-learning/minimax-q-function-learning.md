# Minimax Q-function learning

Minimax Q-function learning estimates the target policy's action-value function for off-policy evaluation by choosing, from a class $\mathcal Q$, the function whose importance-weighted average Bellman error is smallest in the worst case over a class $\mathcal G$ of weight functions used as discriminators.

Use the setting of the [discounted state-action density ratio](discounted-state-action-density-ratio.md): finite $\mathcal X=S\times A$, discount $\gamma\in[0,1)$, initial distribution $d_0$, target policy $\pi_e$, and data tuples $(s,a,r,s')\sim d_{\pi_b}$. For $q:\mathcal X\to\mathbb R$ write $q(s,\pi_e)=\mathbb E_{a\sim\pi_e(\cdot\mid s)}[q(s,a)]$.

**Loss and value estimate.** For $q,g:\mathcal X\to\mathbb R$,

$$
L_{\mathrm q}(q,g)=\mathbb E_{d_{\pi_b}}\Big[g(s,a)\big(r+\gamma\,q(s',\pi_e)-q(s,a)\big)\Big],
\qquad
R_{\mathrm q}[q]=(1-\gamma)\,\mathbb E_{s\sim d_0}\big[q(s,\pi_e)\big],
$$

and $L_{\mathrm q,n}$ is $L_{\mathrm q}$ with $\mathbb E_{d_{\pi_b}}$ replaced by the empirical average over the $n$ tuples. $R_{\mathrm q}[q]$ is the normalized return that $q$ would give if it were $Q^{\pi_e}$; it needs only $d_0$.

**Estimator.** Given classes $\mathcal Q$ and $\mathcal G$ of functions $\mathcal X\to\mathbb R$,

$$
\hat q=\operatorname*{arg\,min}_{q\in\mathcal Q}\max_{g\in\mathcal G}L_{\mathrm q}(q,g)^{2},
\qquad
\hat q_n=\operatorname*{arg\,min}_{q\in\mathcal Q}\max_{g\in\mathcal G}L_{\mathrm q,n}(q,g)^{2},
$$

and the off-policy estimate is $R_{\mathrm q}[\hat q_n]$. The estimator does not use $\pi_b$.

When $g$ is the density ratio from $d_{\pi_b}$ to a distribution $\nu$, $L_{\mathrm q}(q,g)$ is the average Bellman error $\mathbb E_\nu[r+\gamma q(s',\pi_e)-q(s,a)]$. The action value $Q^{\pi_e}$ satisfies $L_{\mathrm q}(Q^{\pi_e},g)=0$ for every $g$, and if $d_{\pi_b}(s,a)>0$ for all $(s,a)$ it is the only function that does (Uehara, Huang and Jiang, Lemma 4). With $\mathcal G=\{g:\mathbb E_{d_{\pi_b}}[g^2]\le 1\}$, $\max_g L_{\mathrm q}(q,g)^2$ is the squared Bellman error $\mathbb E_{d_{\pi_b}}[((B^{\pi_e}q)(s,a)-q(s,a))^2]$ (their Example 5), and with linear $\mathcal Q$ and $\mathcal G$ on common features $\hat q$ is LSTDQ.

## Depends on

- [Discounted state-action density ratio](discounted-state-action-density-ratio.md)
- [Action value of a stochastic policy](../performance-difference-lemma/stoch-qvalue.md)

## Proof depends on

None. This page is a definition.

## Expansion

The loss swaps the roles of the two function classes in [minimax weight learning](minimax-weight-learning.md): there the unknown $Q^{\pi_e}$ is replaced by discriminators, here the unknown $w_{\pi_e/\pi_b}$ is. Taking $g=w_{\pi_e/\pi_b}$ turns $L_{\mathrm q}(q,g)$ into the average Bellman error under $d_{\pi_e,\gamma}$, which equals $R_{\pi_e}-R_{\mathrm q}[q]$ by a telescoping argument over the discounted occupancy.

## Sources

- M. Uehara, J. Huang and N. Jiang, *Minimax Weight and Q-Function Learning for Off-Policy Evaluation*, Proceedings of the 37th International Conference on Machine Learning, PMLR 119:9659–9668 (2020). [arXiv:1910.12809v4](https://arxiv.org/abs/1910.12809v4), §5, Eq. (12), the MQL loss and estimator, Lemma 4, Examples 5 and 7; proofs in Appendix B.
