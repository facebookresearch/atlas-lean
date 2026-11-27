# Bellman-consistent pessimism

Bellman-consistent pessimism is an offline policy-optimization rule: for each candidate policy it keeps the version space of value functions whose estimated Bellman error for that policy is small, scores the policy by the smallest initial-state value in the version space, and returns the policy with the best pessimistic score.

Use the setting of the [Bellman-consistent distribution-shift coefficient](bellman-consistent-distribution-shift.md): a discounted MDP with finite $S$, $A$, rewards $R(s,a)\in[0,R_{\max}]$, discount $\gamma\in[0,1)$, deterministic initial state $s_0$, $V_{\max}=R_{\max}/(1-\gamma)$, a finite nonempty policy class $\Pi\subseteq(S\to\Delta(A))$ and a finite nonempty value-function class $\mathcal F\subseteq(S\times A\to[0,V_{\max}])$. The dataset $\mathcal D$ consists of $n\ge1$ independent tuples $(s,a,r,s')$ with $(s,a)\sim\mu$, $r=R(s,a)$ and $s'\sim P(\cdot\mid s,a)$. For a policy $\pi$, $J(\pi)=\mathbb E[\sum_{t\ge0}\gamma^t r_t\mid\pi]$ from $s_0$.

**Empirical Bellman error.** For $f,f'\in\mathcal F$ and $\pi\in\Pi$ let

$$
\mathcal L(f',f,\pi;\mathcal D)=\frac1n\sum_{(s,a,r,s')\in\mathcal D}\big(f'(s,a)-r-\gamma f(s',\pi)\big)^2,
\qquad
\mathcal E(f,\pi;\mathcal D)=\mathcal L(f,f,\pi;\mathcal D)-\min_{f'\in\mathcal F}\mathcal L(f',f,\pi;\mathcal D).
$$

Subtracting the best regression fit removes the conditional variance of the target, so $\mathcal E$ estimates the squared Bellman error $\|f-\mathcal T^\pi f\|_{2,\mu}^2$ when $\mathcal F$ is approximately complete.

**Algorithm.** For a threshold $\varepsilon>0$, the version space of $\pi$ is $\mathcal F_{\pi,\varepsilon}=\{f\in\mathcal F:\mathcal E(f,\pi;\mathcal D)\le\varepsilon\}$, and the output is

$$
\hat\pi=\operatorname*{arg\,max}_{\pi\in\Pi}\ \min_{f\in\mathcal F_{\pi,\varepsilon}}f(s_0,\pi).
$$

The analysis also uses $f_{\pi,\min}=\operatorname{arg\,min}_{f\in\mathcal F_{\pi,\varepsilon}}f(s_0,\pi)$, $f_{\pi,\max}=\operatorname{arg\,max}_{f\in\mathcal F_{\pi,\varepsilon}}f(s_0,\pi)$ and the width $\Delta f_\pi=f_{\pi,\max}-f_{\pi,\min}$. Since $\Pi$ and $\mathcal F$ are finite, the maxima and minima above are attained whenever the sets they range over are nonempty, so the rule is defined when every version space $\mathcal F_{\pi,\varepsilon}$ is nonempty; the source does not discuss an empty version space. With the threshold $\varepsilon=\varepsilon_r$ of the [regret bound](bellman-consistent-pessimism-regret-bound.md), the source's Theorem A.1 bounds $\mathcal E(f_\pi,\pi;\mathcal D)$ by $\varepsilon_r$ for the function $f_\pi\in\mathcal F$ that best approximates $Q^\pi$, so on the event where that bound holds for every $\pi$, each version space contains $f_\pi$. The pessimism is applied only at the initial state and only among Bellman-consistent functions, unlike pointwise penalties; the rule is information-theoretic, since it evaluates every policy in $\Pi$.

## Depends on

- [Bellman-consistent distribution-shift coefficient](bellman-consistent-distribution-shift.md)

## Proof depends on

None. This page is a definition.

## Expansion

If $Q^\pi\in\mathcal F_{\pi,\varepsilon}$ for every $\pi\in\Pi$, then $\min_{f\in\mathcal F_{\pi,\varepsilon}}f(s_0,\pi)\le J(\pi)$ for all $\pi$, so the score is a lower confidence bound, and for any comparator $\pi$ the regret $J(\pi)-J(\hat\pi)$ is at most the width $\Delta f_\pi(s_0,\pi)$ of the comparator's version space.

## Sources

- T. Xie, C.-A. Cheng, N. Jiang, P. Mineiro and A. Agarwal, *Bellman-consistent Pessimism for Offline Reinforcement Learning*, Advances in Neural Information Processing Systems 34 (NeurIPS 2021), pp. 6683–6694. [arXiv:2106.06926v6](https://arxiv.org/abs/2106.06926v6), §2 (setting, finite classes) and §3, Eqs. (3.1)–(3.2) and the definitions of $f_{\pi,\min}$, $f_{\pi,\max}$ and $\Delta f_\pi$; Appendix A, Theorem A.1; the numbering matches the [conference version](https://proceedings.neurips.cc/paper/2021/file/34f98c7c5d7063181da890ea8d25265a-Paper.pdf).
