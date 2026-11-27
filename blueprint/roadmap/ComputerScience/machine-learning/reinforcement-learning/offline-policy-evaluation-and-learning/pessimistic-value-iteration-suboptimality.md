# Suboptimality bound for pessimistic value iteration

On the event where its penalties bound the errors of the estimated Bellman backups, pessimistic value iteration has suboptimality at most twice the expected total penalty along the optimal policy's trajectory, so only uncertainty about the optimal policy's own state-action pairs enters.

Use the setting and notation of [pessimistic value iteration](pessimistic-value-iteration.md): an episodic MDP of horizon $H$ with rewards in $[0,1]$, a dataset $\mathcal D$ with law $\mathbb P_{\mathcal D}$, estimated backups $\widehat{\mathbb B}_h\widehat V_{h+1}$, penalties $\Gamma_h$, the event $\mathcal E$, and the output $\mathrm{Pess}(\mathcal D)$ of the meta-algorithm.

**Theorem (Jin, Yang and Wang, Theorem 4.2).** Suppose $\{\Gamma_h\}_{h=1}^{H}$ in the algorithm is a $\xi$-uncertainty quantifier, so that $\mathbb P_{\mathcal D}(\mathcal E)\ge1-\xi$. On $\mathcal E$, for every $x\in S$,

$$
\mathrm{SubOpt}\big(\mathrm{Pess}(\mathcal D);x\big)\le2\sum_{h=1}^{H}\mathbb E_{\pi^*}\big[\Gamma_h(s_h,a_h)\,\big|\,s_1=x\big],
$$

where $\mathbb E_{\pi^*}$ is over the trajectory of $\pi^*$ in the true MDP, with the data-dependent functions $\Gamma_h$ held fixed.

The bound involves neither a concentrability coefficient nor the learned policy's trajectories: if the data cover the pairs that $\pi^*$ visits, $\Gamma_h$ is small there regardless of coverage elsewhere. A concrete instance must still construct a valid quantifier, as the [linear-MDP version](pessimistic-value-iteration-in-linear-mdps.md) does; the event $\mathcal E$ concerns the data-dependent $\widehat V_{h+1}$, which is why a uniform concentration argument is needed there.

## Depends on

- [Pessimistic value iteration](pessimistic-value-iteration.md)

## Proof depends on

None. The proof needs an external prerequisite: the extended value-difference lemma for episodic MDPs with step-dependent kernels and stochastic policies (Q. Cai, Z. Yang, C. Jin and Z. Wang, *Provably Efficient Exploration in Policy Optimization*, ICML 2020), stated as Lemma A.1 of arXiv:2012.15085v3; the discounted performance difference lemma does not cover this setting.

## Expansion

Let $\iota_h=\mathbb B_h\widehat V_{h+1}-\widehat Q_h$. The suboptimality decomposition (their Lemma 3.1) writes $\mathrm{SubOpt}(\hat\pi;x)$ as $-\sum_h\mathbb E_{\hat\pi}[\iota_h]+\sum_h\mathbb E_{\pi^*}[\iota_h]$ plus an optimization term that is nonpositive because $\hat\pi$ is greedy for $\widehat Q_h$. On $\mathcal E$, pessimism and truncation give $0\le\iota_h\le2\Gamma_h$ pointwise (their Lemma 5.1): the lower bound because $\widehat Q_h\le\overline Q_h\le\mathbb B_h\widehat V_{h+1}$, the upper bound because $\overline Q_h\ge\mathbb B_h\widehat V_{h+1}-2\Gamma_h$ and truncation at $0$ and at $H-h+1$ only moves $\widehat Q_h$ towards $\mathbb B_h\widehat V_{h+1}$, which lies in $[0,H-h+1]$. The first sum is then nonpositive and the second at most $2\sum_h\mathbb E_{\pi^*}[\Gamma_h]$.

## Sources

- Y. Jin, Z. Yang and Z. Wang, *Is Pessimism Provably Efficient for Offline RL?*, Proceedings of the 38th International Conference on Machine Learning, PMLR 139:5084–5096 (2021). [arXiv:2012.15085v3](https://arxiv.org/abs/2012.15085v3), §3.1, Lemma 3.1; §4.1, Theorem 4.2; §5.1, Lemma 5.1; Appendix A (Lemma A.1) and Appendix B.1 (proof of Lemma 5.1). Lemma 3.1 and Theorem 4.2 carry the same numbers in the conference version, where the proof of Theorem 4.2 is sketched in Section C.1 and Lemma 3.1 is proved in Appendix D; the §5 and Appendix A–B locators are those of arXiv v3 only.
