# Regret bound for Bellman-consistent pessimism

With the version-space threshold set by sample size, realizability and completeness errors, Bellman-consistent pessimism competes with every policy in its class: the regret against $\pi$ splits into an on-support term of order $\frac{V_{\max}\sqrt{C_2}}{1-\gamma}\sqrt{\log(|\mathcal F||\Pi|/\delta)/n}$ and an off-support bias term.

Use the setting and notation of [Bellman-consistent pessimism](bellman-consistent-pessimism.md) and the [Bellman-consistent distribution-shift coefficient](bellman-consistent-distribution-shift.md). Let $d_\pi$ be the normalized discounted state-action occupancy of $\pi$ from $s_0$, and $(\mathcal P^\pi f)(s,a)=\mathbb E_{s'\sim P(\cdot\mid s,a)}[f(s',\pi)]$. Assume:

- *Realizability (Assumption 1).* For every $\pi\in\Pi$, $\inf_{f\in\mathcal F}\sup_{\nu}\|f-\mathcal T^\pi f\|_{2,\nu}^2\le\varepsilon_{\mathcal F}$, the supremum over the admissible distributions $\nu\in\{d_{\pi'}:\pi'\in\Pi\}\cup\{\mu\}$; this holds with $\varepsilon_{\mathcal F}=0$ if $Q^\pi\in\mathcal F$ for all $\pi\in\Pi$.
- *Completeness (Assumption 2).* For every $\pi\in\Pi$, $\sup_{f\in\mathcal F}\inf_{f'\in\mathcal F}\|f'-\mathcal T^\pi f\|_{2,\mu}^2\le\varepsilon_{\mathcal F,\mathcal F}$; completeness is measured under $\mu$ only.

Set

$$
\varepsilon_r=\frac{139\,V_{\max}^2\log\frac{|\mathcal F||\Pi|}{\delta}}{n}+39\,\varepsilon_{\mathcal F}.
$$

**Theorem (Xie, Cheng, Jiang, Mineiro and Agarwal, Theorem 3.1).** Let $\varepsilon=\varepsilon_r$ and let $\hat\pi$ be the output of Bellman-consistent pessimism. Then for any policy $\pi\in\Pi$ and any constant $C_2\ge1$, with probability at least $1-\delta$, every version space $\mathcal F_{\pi',\varepsilon_r}$, $\pi'\in\Pi$, is nonempty, so that $\hat\pi$ is defined, and

$$
J(\pi)-J(\hat\pi)\le O\!\left(\frac{V_{\max}\sqrt{C_2}}{1-\gamma}\sqrt{\frac{\log\frac{|\mathcal F||\Pi|}{\delta}}{n}}+\frac{\sqrt{C_2(\varepsilon_{\mathcal F,\mathcal F}+\varepsilon_{\mathcal F})}}{1-\gamma}\right)
+\frac{1}{1-\gamma}\min_{\nu:\ \mathscr C(\nu;\mu,\mathcal F,\pi)\le C_2}\ \sum_{(s,a)\in S\times A}(d_\pi\setminus\nu)(s,a)\Big[\Delta f_\pi(s,a)-\gamma(\mathcal P^\pi\Delta f_\pi)(s,a)\Big],
$$

where $(d_\pi\setminus\nu)(s,a)=\max(d_\pi(s,a)-\nu(s,a),0)$ and the minimum is over distributions $\nu$ on $S\times A$.

The nonemptiness is part of the source's argument, not an added assumption: its proof works on the event of its Theorem A.1, built from Bernstein's inequality with a union bound over $\mathcal F\times\mathcal F$ and $\mathcal F\times\Pi$, on which each $\mathcal F_{\pi',\varepsilon_r}$ contains the function $f_{\pi'}$ of that theorem (their Lemma B.1). Outside that event, of probability at most $\delta$, the theorem claims nothing: some version space may be empty, leaving $\hat\pi$ undefined, or the bound may fail.

The first term is the on-support error, the second the off-support error. The threshold $C_2$ is a device of the analysis, not an input of the algorithm; the source describes the bound as selecting the best bias-variance split in hindsight. The off-support error vanishes when $\mathscr C(d_\pi;\mu,\mathcal F,\pi)\le C_2$ (take $\nu=d_\pi$) or when $\Delta f_\pi-\gamma\mathcal P^\pi\Delta f_\pi\equiv0$ (their Corollary 1); the first case gives the [single-policy coverage guarantee](bellman-consistent-pessimism-single-policy-coverage.md). The threshold requires knowing $\varepsilon_{\mathcal F}$.

## Depends on

- [Bellman-consistent pessimism](bellman-consistent-pessimism.md)
- [Bellman-consistent distribution-shift coefficient](bellman-consistent-distribution-shift.md)
- [Discounted state-action occupancy of a row-stochastic policy](../stochastic-policies-and-discounted-occupancy/occupancy.md)

## Proof depends on

- [Occupancy averages](../stochastic-policies-and-discounted-occupancy/sum-visitation-mul.md)
- [Bernstein's bound on the moment generating function of a bounded variable](../../../../Probability/concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/mgf-le-of-abs-le.md)
- [Sums of independent sub-exponential variables](../../../../Probability/concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/sum-of-i-indep-fun.md)
- [Sub-exponential tail bound, Gaussian regime](../../../../Probability/concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/measure-real-ge-le-of-le.md)
- [Sub-exponential tail bound, exponential regime](../../../../Probability/concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/measure-real-ge-le-of-ge.md)

## Expansion

Bernstein's inequality with a union bound over $\mathcal F\times\mathcal F$ and $\mathcal F\times\Pi$ (their Appendix A) shows that, with the threshold $\varepsilon_r$, each version space $\mathcal F_{\pi,\varepsilon}$ contains a near-best approximation of $Q^\pi$ and that every member has small Bellman error under $\mu$. Then $J(\pi)-J(\hat\pi)$ is at most $\max_{f\in\mathcal F_{\pi,\varepsilon}}f(s_0,\pi)-\min_{f\in\mathcal F_{\hat\pi,\varepsilon}}f(s_0,\hat\pi)$ plus approximation error, and the optimality of $\hat\pi$ replaces $\hat\pi$ by $\pi$ in the second term. A telescoping identity writes the resulting width $\Delta f_\pi(s_0,\pi)$ as $\frac1{1-\gamma}\mathbb E_{d_\pi}[\Delta f_\pi-\gamma\mathcal P^\pi\Delta f_\pi]$, a difference of Bellman errors under $d_\pi$. Splitting $d_\pi$ into the part covered by some $\nu$ with $\mathscr C(\nu;\mu,\mathcal F,\pi)\le C_2$ and the remainder $d_\pi\setminus\nu$ moves the covered part to $\mu$ at cost $\sqrt{C_2}$ and leaves the remainder as the off-support term. The source applies Bernstein's inequality to averages of $n$ independent bounded variables, together with a union bound over the finite classes $\mathcal F$ and $\Pi$; on the graph this is the chain from Bernstein's moment-generating-function bound for one bounded centred variable, through sums of independent sub-exponential variables, to the two sub-exponential tail bounds, which gives the same inequality up to absolute constants.

## Sources

- T. Xie, C.-A. Cheng, N. Jiang, P. Mineiro and A. Agarwal, *Bellman-consistent Pessimism for Offline Reinforcement Learning*, Advances in Neural Information Processing Systems 34 (NeurIPS 2021), pp. 6683–6694. [arXiv:2106.06926v6](https://arxiv.org/abs/2106.06926v6), §2, Assumptions 1–2; §3, Eq. (3.3), Theorem 3.1, Corollary 1 and the proof sketch; Appendix A (Theorem A.1 and the concentration of the empirical Bellman error, Bernstein with union bounds) and Appendix B (Lemmas B.1–B.3 and the proof of Theorem 3.1); these numbers, including the appendix letters, match the [conference version](https://proceedings.neurips.cc/paper/2021/file/34f98c7c5d7063181da890ea8d25265a-Paper.pdf) and its [supplement](https://papers.nips.cc/paper_files/paper/2021/file/34f98c7c5d7063181da890ea8d25265a-Supplemental.pdf).
