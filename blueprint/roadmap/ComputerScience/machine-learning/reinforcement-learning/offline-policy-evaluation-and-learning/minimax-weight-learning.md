# Minimax weight learning

Minimax weight learning estimates the state-action density ratio for off-policy evaluation by choosing, from a weight class $\mathcal W$, the function $w$ that minimizes the worst violation, over a discriminator class $\mathcal F$ of value functions, of a Bellman-derived identity that the true ratio satisfies for every discriminator.

Use the setting of the [discounted state-action density ratio](discounted-state-action-density-ratio.md): finite $\mathcal X=S\times A$, discount $\gamma\in[0,1)$, initial distribution $d_0$, target policy $\pi_e$, and data tuples $(s,a,r,s')\sim d_{\pi_b}$. For $f:\mathcal X\to\mathbb R$ write $f(s,\pi_e)=\mathbb E_{a\sim\pi_e(\cdot\mid s)}[f(s,a)]$.

**Loss.** For $w,f:\mathcal X\to\mathbb R$,

$$
L_{\mathrm w}(w,f)=\mathbb E_{d_{\pi_b}}\big[\gamma\,w(s,a)\,f(s',\pi_e)-w(s,a)\,f(s,a)\big]+(1-\gamma)\,\mathbb E_{s\sim d_0}\big[f(s,\pi_e)\big],
$$

and $L_{\mathrm w,n}(w,f)$ is the same expression with $\mathbb E_{d_{\pi_b}}$ replaced by the empirical average $\mathbb E_n$ over the $n$ tuples; the term in $d_0$ is computed exactly. The value estimate attached to a weight function is

$$
R_{\mathrm w}[w]=\mathbb E_{d_{\pi_b}}\big[w(s,a)\,r\big],\qquad R_{\mathrm w,n}[w]=\mathbb E_n\big[w(s,a)\,r\big].
$$

**Estimator.** Given a weight class $\mathcal W$ and a discriminator class $\mathcal F$ of functions $\mathcal X\to\mathbb R$, the population and sample estimators are

$$
\hat w=\operatorname*{arg\,min}_{w\in\mathcal W}\max_{f\in\mathcal F}L_{\mathrm w}(w,f)^{2},
\qquad
\hat w_n=\operatorname*{arg\,min}_{w\in\mathcal W}\max_{f\in\mathcal F}L_{\mathrm w,n}(w,f)^{2},
$$

and the off-policy estimate is $R_{\mathrm w,n}[\hat w_n]$. The estimator does not use $\pi_b$. The true ratio is a zero of the loss: $L_{\mathrm w}(w_{\pi_e/\pi_b},f)=0$ for every $f$ (Uehara, Huang and Jiang, Lemma 1). With $\gamma=0$ and a reproducing-kernel discriminator class the method reduces to kernel mean matching, and with linear $\mathcal W$ and $\mathcal F$ on common features it gives a closed form related to LSTDQ.

## Depends on

- [Discounted state-action density ratio](discounted-state-action-density-ratio.md)

## Proof depends on

None. This page is a definition.

## Expansion

The loss comes from requiring $R_{\mathrm w}[w]=R_{\pi_e}=(1-\gamma)\mathbb E_{s\sim d_0}[Q^{\pi_e}(s,\pi_e)]$ and replacing the reward by the Bellman equation $\mathbb E[r\mid s,a]=\mathbb E[Q^{\pi_e}(s,a)-\gamma Q^{\pi_e}(s',\pi_e)\mid s,a]$. The result is linear in the unknown $Q^{\pi_e}$, and $L_{\mathrm w}(w,f)$ measures the violation when $Q^{\pi_e}$ is replaced by a test function $f$. For $w=w_{\pi_e/\pi_b}$ the violation vanishes for every $f$ because $d_{\pi_e,\gamma}$ satisfies the flow equation $d_{\pi_e,\gamma}(s')=(1-\gamma)d_0(s')+\gamma\sum_{s,a}d_{\pi_e,\gamma}(s,a)P(s'\mid s,a)$.

## Sources

- M. Uehara, J. Huang and N. Jiang, *Minimax Weight and Q-Function Learning for Off-Policy Evaluation*, Proceedings of the 37th International Conference on Machine Learning, PMLR 119:9659–9668 (2020). [arXiv:1910.12809v4](https://arxiv.org/abs/1910.12809v4), §4, Eqs. (5)–(10), Lemma 1, Example 2 and §4.2; formal version of Lemma 1 as Lemmas 11–12 in Appendix A.
