# Error bound for fitted Q-iteration

With batch data whose distribution has concentrability coefficient $C$ and a finite value-function class that is approximately closed under the Bellman optimality operator, the greedy policy of fitted Q-iteration after $k$ iterations is, with probability at least $1-\delta$, within $O\big(\frac{V_{\max}}{(1-\gamma)^2}\sqrt{C\ln(|\mathcal F|/\delta)/n}\big)$ of optimal, up to completeness-error and $\gamma^k$ terms.

**Setting.** Use the MDP $M=(S,A,P,R,\gamma,\eta_1)$ of the [concentrability coefficient over admissible distributions](concentrability-over-admissible-distributions.md): finite nonempty $S$ and $A$, deterministic rewards $R(s,a)\in[0,R_{\max}]$, $\gamma\in[0,1)$, $V_{\max}=R_{\max}/(1-\gamma)$. For a policy $\pi$, $v^\pi=\mathbb E[\sum_{h\ge1}\gamma^{h-1}r_h\mid s_1\sim\eta_1,\pi]$, and $v^\star$ is the largest value, attained by a deterministic optimal policy. For $f:S\times A\to\mathbb R$ let $V_f(s)=\max_a f(s,a)$, let $\pi_f$ be a policy greedy for $f$ (any maximizing action), and let

$$
(\mathcal Tf)(s,a)=R(s,a)+\gamma\,\mathbb E_{s'\sim P(s,a)}\big[V_f(s')\big].
$$

The data $D$ are $n\ge1$ tuples $(s,a,r,s')$ with $(s,a)$ drawn independently from a distribution $\mu$ on $S\times A$, $r=R(s,a)$ and $s'\sim P(s,a)$. Write $\|g\|_{2,\mu}^2=\mathbb E_{\mu}[g^2]$.

**Fitted Q-iteration.** Given a finite nonempty class $\mathcal F$ of functions $S\times A\to[0,V_{\max}]$, start from any $f_0\in\mathcal F$ and for $k\ge1$ let $f_k$ be any minimizer over $f\in\mathcal F$ of the regression loss

$$
\mathcal L_D(f;f_{k-1})=\frac{1}{n}\sum_{(s,a,r,s')\in D}\big(f(s,a)-r-\gamma V_{f_{k-1}}(s')\big)^2 .
$$

The output after $k$ iterations is $\pi_{f_k}$.

**Assumptions.** $\mu$ satisfies concentrability with constant $C$ (Assumption 1), and $\mathcal F$ is approximately complete (Assumption 3 with $\mathcal G=\mathcal F$) with inherent Bellman error

$$
\epsilon_{\mathcal F,\mathcal F}=\sup_{f\in\mathcal F}\ \inf_{f'\in\mathcal F}\ \|f'-\mathcal Tf\|_{2,\mu}^2 .
$$

**Theorem (Chen and Jiang, Theorem 11).** With probability at least $1-\delta$ over $D$, the output after $k$ iterations satisfies

$$
v^\star-v^{\pi_{f_k}}\le O\!\left(\frac{V_{\max}}{(1-\gamma)^2}\left(\sqrt{\frac{C\ln\frac{|\mathcal F|}{\delta}}{n}}+\sqrt[4]{\frac{C\ln\frac{|\mathcal F|}{\delta}}{n}\,\epsilon_{\mathcal F,\mathcal F}}\right)\right)+\frac{2\big(\sqrt{C\epsilon_{\mathcal F,\mathcal F}}+\gamma^{k}(1-\gamma)V_{\max}\big)}{(1-\gamma)^2},
$$

where $O(\cdot)$ hides only an absolute constant.

With exact completeness, $\epsilon_{\mathcal F,\mathcal F}=0$ ($\mathcal Tf\in\mathcal F$ for every $f\in\mathcal F$), this gives their Theorem 2: a sample size $n=O\big(C\ln\frac{|\mathcal F|}{\delta}/(\epsilon^2(1-\gamma)^4)\big)$ makes $v^\star-v^{\pi_{f_k}}\le\epsilon V_{\max}$ with probability at least $1-\delta$ once $k$ is large enough for the $\gamma^k$ term. The middle term is the geometric mean of the statistical and approximation terms, so it never dominates. Completeness is a closure condition, not monotone in $\mathcal F$: adding functions keeps realizability $Q^\star\in\mathcal F$ but can break completeness.

## Depends on

- [Concentrability coefficient over admissible distributions](concentrability-over-admissible-distributions.md)
- [Value of a stochastic policy](../stochastic-policies-and-discounted-occupancy/stoch-value.md)
- [Optimal value of a discounted Markov decision process](../../../heuristic-search-and-planning/value-iteration/optimal-value.md)

## Proof depends on

- [Performance difference lemma](../performance-difference-lemma/performance-difference.md)
- [Bernstein's bound on the moment generating function of a bounded variable](../../../../Probability/concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/mgf-le-of-abs-le.md)
- [Sums of independent sub-exponential variables](../../../../Probability/concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/sum-of-i-indep-fun.md)
- [Sub-exponential tail bound, Gaussian regime](../../../../Probability/concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/measure-real-ge-le-of-le.md)
- [Sub-exponential tail bound, exponential regime](../../../../Probability/concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/measure-real-ge-le-of-ge.md)

## Expansion

By the performance difference lemma, $v^\star-v^{\pi_f}$ is at most $\sum_h\gamma^{h-1}\big(\|Q^\star-f\|_{2,\eta_h^{\pi_f}\times\pi^\star}+\|Q^\star-f\|_{2,\eta_h^{\pi_f}\times\pi_f}\big)$, a sum of errors under admissible distributions (their Lemma 13). Concentrability moves each term to $\mu$ at the cost $\sqrt C$, and a non-expansion property of the max (Lemma 14) gives $\|f_k-Q^\star\|_{2,\nu}\le\sqrt C\|f_k-\mathcal Tf_{k-1}\|_{2,\mu}+\gamma\|f_{k-1}-Q^\star\|_{2,\nu'}$ for admissible $\nu$ and some admissible $\nu'$ (Lemma 15); unrolling over $k$ iterations produces the $\gamma^k$ term. Each regression error $\|f_k-\mathcal Tf_{k-1}\|_{2,\mu}^2$ is bounded uniformly over $f_{k-1}\in\mathcal F$ by a Bernstein-based fast-rate deviation bound for least squares with the approximately realizable target $\mathcal Tf_{k-1}$ (Lemma 16), which reuses the same data in every iteration. The source applies Bernstein's inequality to averages of $n$ independent bounded variables, together with a union bound over the finite classes; on the graph this is the chain from Bernstein's moment-generating-function bound for one bounded centred variable, through sums of independent sub-exponential variables, to the two sub-exponential tail bounds, which gives the same inequality up to absolute constants.

## Sources

- J. Chen and N. Jiang, *Information-Theoretic Considerations in Batch Reinforcement Learning*, Proceedings of the 36th International Conference on Machine Learning, PMLR 97:1042–1051 (2019). [arXiv:1905.00360v1](https://arxiv.org/abs/1905.00360v1), §2.2, Eq. (2) (fitted Q-iteration); §3.2, Assumptions 1–3, Theorem 2 and the remarks after Assumption 3; Appendix C, Theorem 11 and Lemmas 12–16.
