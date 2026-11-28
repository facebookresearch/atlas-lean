# Pessimistic value iteration in linear MDPs

For data compliant with a $d$-dimensional linear MDP and measurable, attained greedy steps, pessimistic value iteration with unit ridge regularization and $\Gamma_h=\beta(\phi^\top\Lambda_h^{-1}\phi)^{1/2}$, $\beta=c\,dH\sqrt{\log(2dHK/\xi)}$, has suboptimality at most $2\beta\sum_h\mathbb E_{\pi^*}[(\phi^\top\Lambda_h^{-1}\phi)^{1/2}]$ with probability at least $1-\xi$, for sufficiently large absolute $c$.

Use the episodic setting, the compliance condition on the dataset $\mathcal D$ of $K$ trajectories, and the meta-algorithm of [pessimistic value iteration](pessimistic-value-iteration.md), with rewards $r_h\in[0,1]$. Assume that the estimated quantities and chosen maximizers are jointly measurable in the state and the data, and that the maximization in the algorithm has a solution for every $h$, every $x$ and every dataset, so that the output policy is a measurable kernel and $\widehat V_{h+1}$ and $\mathrm{Pess}(\mathcal D)$ are defined; also assume that the event $\mathcal E$ of statement (i) is measurable. The source discusses neither existence nor measurability; a solution exists when $A$ is finite and nonempty, and a fixed tie-breaking order among actions then makes the choice jointly measurable whenever the estimated values are.

**Linear MDP (Jin, Yang and Wang, Definition 4.3).** The episodic MDP $(S,A,H,\mathcal P,r)$ is a linear MDP with a known feature map $\phi:S\times A\to\mathbb R^{d}$ if for each $h\in[H]$ there are $d$ unknown signed measures $\mu_h=(\mu^{(1)}_h,\ldots,\mu^{(d)}_h)$ over $S$ and an unknown vector $\theta_h\in\mathbb R^{d}$ with

$$
\mathcal P_h(x'\mid x,a)=\langle\phi(x,a),\mu_h(x')\rangle,
\qquad
\mathbb E\big[r_h(s_h,a_h)\mid s_h=x,a_h=a\big]=\langle\phi(x,a),\theta_h\rangle
$$

for all $(x,a,x')$, where $\|\phi(x,a)\|\le1$ for all $(x,a)$ and $\max\{\|\mu_h(S)\|,\|\theta_h\|\}\le\sqrt d$, with $\|\mu_h(S)\|=\int_S\|\mu_h(x)\|\,dx$.

**Algorithm (Algorithm 2).** With $\widehat V_{H+1}\equiv0$ and, for $h=H,\ldots,1$,

$$
\Lambda_h=\sum_{\tau=1}^{K}\phi(x^\tau_h,a^\tau_h)\phi(x^\tau_h,a^\tau_h)^{\top}+\lambda I,
\qquad
\hat w_h=\Lambda_h^{-1}\sum_{\tau=1}^{K}\phi(x^\tau_h,a^\tau_h)\big(r^\tau_h+\widehat V_{h+1}(x^\tau_{h+1})\big),
$$

the meta-algorithm is run with $(\widehat{\mathbb B}_h\widehat V_{h+1})(x,a)=\phi(x,a)^{\top}\hat w_h$, the ridge-regression minimizer of $\sum_\tau(r^\tau_h+\widehat V_{h+1}(x^\tau_{h+1})-\phi(x^\tau_h,a^\tau_h)^{\top}w)^2+\lambda\|w\|_2^2$, and $\Gamma_h(x,a)=\beta\,(\phi(x,a)^{\top}\Lambda_h^{-1}\phi(x,a))^{1/2}$.

**Theorem (Jin, Yang and Wang, Theorem 4.4).** Suppose the dataset is compliant with the MDP (Assumption 2.2) and the MDP is a linear MDP. Set $\lambda=1$ and $\beta=c\cdot dH\sqrt\zeta$ with $\zeta=\log(2dHK/\xi)$, where $c>0$ is an absolute constant and $\xi\in(0,1)$. Then (i) $\{\Gamma_h\}_{h=1}^{H}$ is a $\xi$-uncertainty quantifier, and hence (ii) on the event $\mathcal E$, which has $\mathbb P_{\mathcal D}(\mathcal E)\ge1-\xi$, for every $x\in S$,

$$
\mathrm{SubOpt}\big(\mathrm{Pess}(\mathcal D);x\big)\le2\beta\sum_{h=1}^{H}\mathbb E_{\pi^*}\Big[\big(\phi(s_h,a_h)^{\top}\Lambda_h^{-1}\phi(s_h,a_h)\big)^{1/2}\,\Big|\,s_1=x\Big],
$$

where $\mathbb E_{\pi^*}$ is over the trajectory of $\pi^*$ in the true MDP with the data-dependent matrices $\Lambda_h$ held fixed. Off $\mathcal E$ no bound is claimed.

No coverage assumption is made: the bound depends on the data only through how well $\Lambda_h$ covers the features along the optimal policy's trajectory. In the tabular case, with indicator features and deterministic transitions, the $h$-th term is $(N_h(s^*_h,a^*_h)+\lambda)^{-1/2}$ for the count of the optimal pair at step $h$. If $\Lambda_h\succeq I+c^{\dagger}K\,\mathbb E_{\pi^*}[\phi\phi^{\top}\mid s_1=x]$ for all $x$ and $h$ with probability at least $1-\xi/2$, then, with $\lambda=1$ and $\beta=c\,dH\sqrt{\zeta'}$ for $\zeta'=\log(4dHK/\xi)$, with probability at least $1-\xi$ the suboptimality is at most $c'\,d^{3/2}H^2K^{-1/2}\sqrt{\zeta'}$ for all $x$, with $c'$ depending only on $c^{\dagger}$ and $c$ (their Corollary 4.5). The rate also has a matching information-theoretic lower bound up to $\beta$ and constants (their Theorem 4.7, Theorem 4.6 of the conference version).

## Depends on

- [Pessimistic value iteration](pessimistic-value-iteration.md)

## Proof depends on

- [Suboptimality bound for pessimistic value iteration](pessimistic-value-iteration-suboptimality.md)

Part (i) also needs two external prerequisites, as cited by the source: the self-normalized bound for vector-valued martingales (Y. Abbasi-Yadkori, D. Pál and Cs. Szepesvári, *Improved Algorithms for Linear Stochastic Bandits*, NeurIPS 2011; Lemma E.2 of arXiv:2012.15085v3) and the covering-number bound for truncated linear value functions (C. Jin, Z. Yang, Z. Wang and M. I. Jordan, *Provably Efficient Reinforcement Learning with Linear Function Approximation*, COLT 2020, Lemma D.6; Lemma B.3 of arXiv:2012.15085v3).

## Expansion

Part (ii) is the [general suboptimality bound](pessimistic-value-iteration-suboptimality.md) with this $\Gamma_h$. For part (i) (their Lemma 5.2), linearity of the MDP makes $\mathbb B_h\widehat V_{h+1}=\phi^{\top}w_h$ for a weight with $\|w_h\|\le(1+V_{\max})\sqrt d$ whenever $\widehat V_{h+1}$ takes values in $[0,V_{\max}]$ (their Lemma B.1). The backup error $\phi(x,a)^{\top}(\hat w_h-w_h)$ then splits into a regularization term and a noise term, each bounded by a multiple of $\|\phi(x,a)\|_{\Lambda_h^{-1}}=(\phi^{\top}\Lambda_h^{-1}\phi)^{1/2}$. A self-normalized concentration bound for vector-valued martingales, made uniform over the possible $\widehat V_{h+1}$ by a covering argument, controls the noise factor by $O(dH\sqrt\zeta)$ with probability at least $1-\xi$; compliance supplies the martingale structure without independence across trajectories.

## Sources

- Y. Jin, Z. Yang and Z. Wang, *Is Pessimism Provably Efficient for Offline RL?*, Proceedings of the 38th International Conference on Machine Learning, PMLR 139:5084–5096 (2021). [arXiv:2012.15085v3](https://arxiv.org/abs/2012.15085v3), §4.2, Definition 4.3, Eqs. (4.4)–(4.8), Algorithm 2, Theorem 4.4 and the remarks after it, Corollary 4.5; §4.3, Theorem 4.7; §5.2 (Lemma 5.2) and Appendix B (Lemmas B.1–B.3). Definition 4.3, Algorithm 2, Theorem 4.4 and Corollary 4.5 carry the same numbers in the conference version, whose lower bound is Theorem 4.6; there the proof of Theorem 4.4 is sketched in Section C.2 and Corollary 4.5 is proved in Appendix E.3. The §5 and Appendix B locators are those of arXiv v3 only.
