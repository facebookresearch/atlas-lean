# Bellman-consistent pessimism under single-policy coverage

If the data distribution covers the optimal policy in the Bellman-consistent sense, $\mathscr C(d_{\pi^\star};\mu,\mathcal F,\pi^\star)\le C_2$, then Bellman-consistent pessimism returns a policy whose suboptimality is $O\big(\frac{V_{\max}\sqrt{C_2}}{1-\gamma}\sqrt{\log(|\mathcal F||\Pi|/\delta)/n}\big)$ plus approximation error, with no coverage assumption on other policies.

Use the setting, assumptions and threshold $\varepsilon=\varepsilon_r$ of the [regret bound for Bellman-consistent pessimism](bellman-consistent-pessimism-regret-bound.md): finite classes $\Pi$ and $\mathcal F$, realizability error $\varepsilon_{\mathcal F}$ (Assumption 1), completeness error $\varepsilon_{\mathcal F,\mathcal F}$ under $\mu$ (Assumption 2), and $n$ independent tuples from $\mu$. Let $\pi^\star$ be an optimal policy, and assume $\pi^\star\in\Pi$, since the regret bound compares with policies in $\Pi$.

**Theorem (Xie, Cheng, Jiang, Mineiro and Agarwal, Corollary 2).** If $\mathscr C(d_{\pi^\star};\mu,\mathcal F,\pi^\star)\le C_2$ for a constant $C_2\ge 1$, then with probability at least $1-\delta$ every version space $\mathcal F_{\pi,\varepsilon_r}$, $\pi\in\Pi$, is nonempty, so that $\hat\pi$ is defined, and

$$
J(\pi^\star)-J(\hat\pi)\le O\!\left(\frac{V_{\max}\sqrt{C_2}}{1-\gamma}\sqrt{\frac{\log\frac{|\mathcal F||\Pi|}{\delta}}{n}}+\frac{\sqrt{C_2(\varepsilon_{\mathcal F,\mathcal F}+\varepsilon_{\mathcal F})}}{1-\gamma}\right).
$$

Classical analyses that compete with $\pi^\star$ often require $\|\nu/\mu\|_\infty$ to be bounded for every admissible $\nu\in\{d_\pi:\pi\in\Pi\}$; here coverage of one policy suffices, and it is measured through Bellman errors over $\mathcal F$, so it is implied by a bounded [single-policy concentrability coefficient](single-policy-concentrability.md) $\|d_{\pi^\star}/\mu\|_\infty$. The same argument with $\mu=d_{\pi_b}$ for a behavior policy $\pi_b\in\Pi$ gives $C_2=1$ and a bound on $J(\pi_b)-J(\hat\pi)$ (their Corollary 3).

## Depends on

- [Bellman-consistent pessimism](bellman-consistent-pessimism.md)
- [Bellman-consistent distribution-shift coefficient](bellman-consistent-distribution-shift.md)
- [Regret bound for Bellman-consistent pessimism](bellman-consistent-pessimism-regret-bound.md)
- [Discounted state-action occupancy of a row-stochastic policy](../stochastic-policies-and-discounted-occupancy/occupancy.md)
- [Optimal value of a discounted Markov decision process](../../../heuristic-search-and-planning/value-iteration/optimal-value.md)

## Proof depends on

None beyond the statement prerequisites: the proof applies the regret bound listed above.

## Expansion

Apply the regret bound, on its event of probability at least $1-\delta$, with $\pi=\pi^\star$ and choose $\nu=d_{\pi^\star}$ in the minimum. This $\nu$ satisfies the constraint by hypothesis and makes $d_{\pi^\star}\setminus\nu=0$, so the off-support term vanishes and only the on-support term remains.

## Sources

- T. Xie, C.-A. Cheng, N. Jiang, P. Mineiro and A. Agarwal, *Bellman-consistent Pessimism for Offline Reinforcement Learning*, Advances in Neural Information Processing Systems 34 (NeurIPS 2021), pp. 6683–6694. [arXiv:2106.06926v6](https://arxiv.org/abs/2106.06926v6), §3, Corollaries 1–3 and the comparison with the exploratory setting; the numbering matches the [conference version](https://proceedings.neurips.cc/paper/2021/file/34f98c7c5d7063181da890ea8d25265a-Paper.pdf).
