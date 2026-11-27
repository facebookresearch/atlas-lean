# Bellman-consistent distribution-shift coefficient

The Bellman-consistent distribution-shift coefficient $\mathscr C(\nu;\mu,\mathcal F,\pi)$ measures how much the squared Bellman error of a policy $\pi$ can grow, over a value-function class $\mathcal F$, when the state-action distribution changes from the data distribution $\mu$ to $\nu$; it never exceeds the density-ratio bound $\|\nu/\mu\|_\infty$.

**Setting.** An MDP $(S,A,P,R,\gamma,s_0)$ has finite state and action sets $S$ and $A$, transitions $P:S\times A\to\Delta(S)$, reward function $R:S\times A\to[0,R_{\max}]$, discount $\gamma\in[0,1)$ and a deterministic initial state $s_0$; $V_{\max}=R_{\max}/(1-\gamma)$. For a stochastic policy $\pi:S\to\Delta(A)$ and $f:S\times A\to\mathbb R$ write $f(s',\pi)=\mathbb E_{a'\sim\pi(\cdot\mid s')}[f(s',a')]$, and let the policy Bellman operator be

$$
(\mathcal T^\pi f)(s,a)=R(s,a)+\gamma\,\mathbb E_{s'\sim P(\cdot\mid s,a)}\big[f(s',\pi)\big],
$$

whose unique fixed point is the action value $Q^\pi$. For a distribution $\nu$ on $S\times A$, $\|f\|_{2,\nu}^2=\mathbb E_{(s,a)\sim\nu}[f(s,a)^2]$. A value-function class $\mathcal F\subseteq(S\times A\to[0,V_{\max}])$ is given, and $\mu$ is the data distribution on $S\times A$.

**Definition (Xie, Cheng, Jiang, Mineiro and Agarwal, Definition 1).** For a distribution $\nu$ on $S\times A$, the class $\mathcal F$ and a policy $\pi$,

$$
\mathscr C(\nu;\mu,\mathcal F,\pi)=\max_{f\in\mathcal F}\frac{\|f-\mathcal T^\pi f\|_{2,\nu}^2}{\|f-\mathcal T^\pi f\|_{2,\mu}^2}.
$$

Xie et al. take $\mathcal F$ finite in their general results, so the maximum exists; for an infinite class read it as a supremum. The source gives no convention for a vanishing denominator; read a ratio $u/0$ as $0$ when $u=0$ and as $+\infty$ when $u>0$, so that the coefficient is an extended nonnegative real.

For every $\pi$ and $\mathcal F$ the source observes

$$
\mathscr C(\nu;\mu,\mathcal F,\pi)\le\|\nu/\mu\|_\infty=\sup_{s,a}\frac{\nu(s,a)}{\mu(s,a)},
$$

and the left side can be much smaller: distributions that differ only in ways that the Bellman errors of $\pi$ over $\mathcal F$ do not detect admit transfer. A small $\mathscr C(d_\pi;\mu,\mathcal F,\pi)$, with $d_\pi$ the normalized discounted occupancy of $\pi$ from $s_0$, allows accurate evaluation of $\pi$ from data drawn from $\mu$; boundedness for one comparator policy is the function-class analogue of [single-policy concentrability](single-policy-concentrability.md). In linear MDPs, boundedness for all admissible $\nu$ follows from a spectral coverage condition on the feature covariance under $\mu$.

## Depends on

- [Value of a stochastic policy](../stochastic-policies-and-discounted-occupancy/stoch-value.md)
- [Action value of a stochastic policy](../performance-difference-lemma/stoch-qvalue.md)

## Proof depends on

None. This page is a definition.

## Expansion

The bound by $\|\nu/\mu\|_\infty$ is termwise: $\|g\|_{2,\nu}^2=\sum_{(s,a)}g(s,a)^2\nu(s,a)\le\|\nu/\mu\|_\infty\sum_{(s,a)}g(s,a)^2\mu(s,a)$ for $g=f-\mathcal T^\pi f$, and the maximum over $f$ keeps the bound. The coefficient generalizes the feature-covariance measures of distribution shift used for linear function approximation by Agarwal, Kakade, Lee and Mahajan and by Duan, Jia and Wang.

## Sources

- T. Xie, C.-A. Cheng, N. Jiang, P. Mineiro and A. Agarwal, *Bellman-consistent Pessimism for Offline Reinforcement Learning*, Advances in Neural Information Processing Systems 34 (NeurIPS 2021), pp. 6683–6694. [arXiv:2106.06926v6](https://arxiv.org/abs/2106.06926v6), §2, Definition 1 and the inequality and remarks after it, with §3.1 for the linear case; the numbering matches the [conference version](https://proceedings.neurips.cc/paper/2021/file/34f98c7c5d7063181da890ea8d25265a-Paper.pdf).
