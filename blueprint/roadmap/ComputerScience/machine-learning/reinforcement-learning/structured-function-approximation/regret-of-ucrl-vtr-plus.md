# Regret of UCRL-VTR+ in linear mixture MDPs

UCRL-VTR+ combines optimistic value iteration with variance-weighted value-targeted regression. In an inhomogeneous episodic $B$-bounded linear mixture MDP it has regret $\tilde O\big(\sqrt{d^2H^2 + dH^3}\,\sqrt T + d^2H^3 + d^3H^2\big)$ over $T = KH$ steps with probability $1-5\delta$, which is $\tilde O(dH\sqrt T)$ when $d \ge H$ and $T \ge d^4H^2 + d^3H^3$.

**Setting.** $M_{\Theta^\star}$ is an inhomogeneous, episodic, $B$-bounded [linear mixture MDP](linear-mixture-mdp.md) with known admissible features $\phi(s' \mid s,a) \in \mathbb{R}^d$, unknown $\theta^\star_h$ with $\lVert\theta^\star_h\rVert_2 \le B$, known deterministic rewards $r_h \in [0,1]$, countable states and finitely many actions. In episode $k$ the environment picks $s^k_1$ and the agent follows $\pi^k$; the regret after $K$ episodes is $\mathrm{Regret}(M_{\Theta^\star}, K) = \sum_{k=1}^K [V^\ast_1(s^k_1) - V^{\pi^k}_1(s^k_1)]$.

**Algorithm (UCRL-VTR+), in outline.** For each $h$ it keeps two ridge estimates: a weighted first-moment estimate $\hat\theta_{k,h}$, from regressing $V_{j,h+1}(s^j_{h+1})$ on $\phi_{V_{j,h+1}}(s^j_h,a^j_h)$ with weights $\bar\sigma_{j,h}^{-2}$, and an unweighted second-moment estimate $\tilde\theta_{k,h}$, from regressing $V^2_{j,h+1}(s^j_{h+1})$ on $\phi_{V^2_{j,h+1}}(s^j_h,a^j_h)$. The variance estimate (the source's Eq. (5.6)) is

$$
(\bar{\mathbb{V}}_{k,h}V_{k,h+1})(s^k_h,a^k_h) = \big[\langle \phi_{V^2_{k,h+1}}(s^k_h,a^k_h), \tilde\theta_{k,h}\rangle\big]_{[0,H^2]} - \big[\langle \phi_{V_{k,h+1}}(s^k_h,a^k_h), \hat\theta_{k,h}\rangle\big]_{[0,H]}^2,
$$

where $[x]_{[a,b]}$ clips $x$ to $[a,b]$. With an error allowance $E_{k,h}$ (the source's Eq. (5.8)), the algorithm sets $\bar\sigma_{k,h}^2 = \max\{H^2/d,\ (\bar{\mathbb{V}}_{k,h}V_{k,h+1})(s^k_h,a^k_h) + E_{k,h}\}$. The optimistic values are $Q_{k,h} = \min\{H,\ r_h + \langle\hat\theta_{k,h}, \phi_{V_{k,h+1}}\rangle + \hat\beta_k \lVert \hat\Sigma_{k,h}^{-1/2}\phi_{V_{k,h+1}} \rVert_2\}$, where $\hat\Sigma_{k,h}$ is the weighted Gram matrix and $\hat\beta_k$ the confidence radius of the source's Eq. (5.7). The policy is greedy.

**Theorem.** For every $\delta \in (0,1)$, UCRL-VTR+ with confidence parameter $\delta$ and $\lambda = 1/B^2$ has, with probability at least $1 - 5\delta$,

$$
\mathrm{Regret}(M_{\Theta^\star}, K) = \tilde O\Big(\sqrt{d^2H^2 + dH^3}\,\sqrt{T} + d^2H^3 + d^3H^2\Big), \qquad T = KH .
$$

**Reading and scope.** For $d \ge H$ and $T \ge d^4H^2 + d^3H^3$ this is $\tilde O(dH\sqrt T)$, matching the [lower bound for linear mixture MDPs](regret-lower-bound-for-linear-mixture-mdps.md) up to logarithmic factors. The guarantee needs only $0 \le \sum_h r_h \le H$ along trajectories. The horizon dependence is for stage-dependent kernels; the source notes that earlier $\tilde O(dH\sqrt T)$ bounds for UCRL-VTR were for time-homogeneous kernels. Computational cost depends on the feature family. For $\phi(s'\mid s,a) = \psi(s') \odot \mu(s,a)$, with an oracle evaluating $\sum_{s'}\psi(s')V(s')$ through $p(d)$ evaluations of $V$, the total cost is $O(\mathrm{poly}(d)|\mathcal{A}|T)$.

## Depends on

- [Linear mixture MDP](linear-mixture-mdp.md)

## Proof depends on

- [Bernstein-type self-normalized bound for vector-valued martingales](bernstein-self-normalized-bound.md)
- [Elliptical potential lemma](../multi-armed-bandits/linear-bandits/elliptical-potential-lemma.md)
- [Azuma's inequality](../../../../Probability/concentration-inequalities/azuma-inequality.md)

## Expansion

The Bernstein-type bound, applied to the weighted regression whose noise has conditional variance at most $1$ after division by $\bar\sigma_{k,h}$, puts $\theta^\star_h$ in the confidence ellipsoid around $\hat\theta_{k,h}$ for all $(k,h)$. On the same event, two more confidence sets bound the variance estimate's error by $E_{k,h}$ (Lemma 5.2): a ball of radius $\check\beta_k$ around $\hat\theta_{k,h}$ in the $\hat\Sigma_{k,h}$-norm, whose leading term is larger than that of $\hat\beta_k$ by a factor of $\sqrt d$, and a ball of radius $\tilde\beta_k$ around $\tilde\theta_{k,h}$ in the $\tilde\Sigma_{k,h}$-norm. Hence $\bar\sigma_{k,h}^2$ dominates the true conditional variance and $Q_{k,h} \ge Q^\ast_h$. The regret is then bounded by the sum of bonuses $\hat\beta_K \sum_{k,h}\lVert\hat\Sigma_{k,h}^{-1/2}\phi_{V_{k,h+1}}\rVert_2$. Cauchy–Schwarz turns it into $\hat\beta_K\sqrt{dH\sum_{k,h}\bar\sigma^2_{k,h}}$, using the elliptical potential lemma on the weighted features. The law of total variance bounds the total variance of the policies' own values, $\sum_{k,h}(\mathbb{V}_hV^{\pi^k}_{h+1})(s^k_h,a^k_h) \le 3(HT + H^3\log(1/\delta))$ with probability at least $1-\delta$ (Lemma C.3). Lemma C.6 bounds $\sum_{k,h}\bar\sigma^2_{k,h}$ by that total plus $H^2T/d$, a gap term $2H\sum_{k,h}\big(\mathbb{P}_h(V_{k,h+1} - V^{\pi^k}_{h+1})\big)(s^k_h,a^k_h)$ and confidence-width terms; bounding these gives $\sum_{k,h}\bar\sigma^2_{k,h} = \tilde O(HT + H^2T/d + dH^3\sqrt{T})$, and substituting gives the bound. Martingale terms are handled by Azuma–Hoeffding.

A complete expansion adds pages for the law of total variance for episodic MDPs in the form of Lemma C.3 (the source takes it from Jin et al. 2018 and credits the law of total variance to Lattimore and Hutter 2012 and Azar et al. 2013), for the comparison of Lemma C.6, and for the variance-estimate error bound with the radii $\check\beta_k$ (around $\hat\theta_{k,h}$) and $\tilde\beta_k$ (around $\tilde\theta_{k,h}$) (Lemma 5.2).

The source's Remark 5.1 refers to the first-moment estimate as $\check\theta_{k,h}$. Algorithm 2 and Eq. (5.6) use the weighted estimate $\hat\theta_{k,h}$, and this page follows Algorithm 2. The page follows arXiv:2012.08507v2, whose Algorithm 2 caps $Q_{k,h}$ at $H$; the published version clips it to $[0,H]$ and numbers the displayed equations differently.

## Sources

- D. Zhou, Q. Gu and Cs. Szepesvári, "Nearly Minimax Optimal Reinforcement Learning for Linear Mixture Markov Decision Processes", Conference on Learning Theory (COLT 2021), PMLR 134:4532–4576. Numbers from arXiv:2012.08507v2: Section 3 (regret), Section 5.1 (Algorithm 2, Eqs. (5.4)–(5.8), Remark 5.1, Lemma 5.2, computational efficiency), Appendix C.1 (the sets $\check{\mathcal C}_{k,h}$ and $\tilde{\mathcal C}_{k,h}$), Theorem 5.3 with its proof sketch, Remarks 5.4–5.5, Appendix C.2 (Lemmas C.2–C.6). <https://arxiv.org/abs/2012.08507v2>
