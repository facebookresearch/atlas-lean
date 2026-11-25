# Regret of LSVI-UCB in linear MDPs

In a linear MDP with known features and integrated normalization, LSVI-UCB with $\lambda = 1$ and $\beta = c\, dH\sqrt{\iota}$ has regret $O(\sqrt{d^3 H^3 T \iota^2})$ over $T = KH$ steps with probability $1-p$, where $\iota = \log(2dT/p)$; the bound does not depend on the numbers of states or actions, and the algorithm runs in polynomial time.

**Setting.** $(\mathcal{S}, \mathcal{A}, H, \mathbb{P}, r)$ is a [linear MDP](linear-mdp.md) with known feature map $\phi$ (normalized by $\lVert\phi\rVert_2 \le 1$, $\max\{\lVert\mu_h(\mathcal{S})\rVert_2, \lVert\theta_h\rVert_2\} \le \sqrt d$ and the integrated normalization $\lVert \int g\, d\mu_h \rVert_2 \le \sqrt d$ for every measurable $g : \mathcal{S} \to [0,1]$), deterministic rewards in $[0,1]$, finite action set, and stage-dependent kernels $\mathbb{P}_h$. In each episode $k = 1, \dots, K$ an adversary picks the initial state $x^k_1$ and the learner plays a policy $\pi_k$ for $H$ steps. The regret is

$$
\mathrm{Regret}(K) = \sum_{k=1}^{K} \big[ V^\star_1(x^k_1) - V^{\pi_k}_1(x^k_1) \big], \qquad T = KH .
$$

**Theorem.** There is an absolute constant $c > 0$ such that for every $p \in (0,1)$, [LSVI-UCB](lsvi-ucb.md) run with $\lambda = 1$ and $\beta = c \cdot dH\sqrt{\iota}$, $\iota = \log(2dT/p)$, satisfies, with probability at least $1-p$,

$$
\mathrm{Regret}(K) = O\big(\sqrt{d^3 H^3 T \iota^2}\big),
$$

where $O(\cdot)$ hides only absolute constants.

The theorem is printed (Jin et al., Theorem 3.1) under the total-mass normalization alone. Its proof bounds the weights of true action values through Lemma B.1, whose proof uses the integrated normalization (as Agarwal et al. record), so the statement here carries that condition. Agarwal et al. invoke the LSVI-UCB guarantee under this normalization for low-rank MDPs with known embeddings (proof of their Lemma 15).

**Computation.** The guarantee is statistical and computational together: the algorithm uses $O(d^2 H + dAT)$ space and $O(d^2 AKT)$ time, with $A = |\mathcal{A}|$.

**Scope.** The features are known and fixed; nothing is learned about the representation. The lower bound recorded by the source is $\Omega(\sqrt{dH^2T})$, obtained from the tabular case with nonstationary transitions (with $d = |\mathcal{S}||\mathcal{A}|$), so the dependence on $d$ and $H$ is not shown to be optimal.

## Depends on

- [Linear MDP](linear-mdp.md)
- [LSVI-UCB](lsvi-ucb.md)

## Proof depends on

- [Action values are linear in a linear MDP](action-values-are-linear-in-a-linear-mdp.md)
- [Uniform self-normalized bound over a value-function class](uniform-self-normalized-bound-over-a-value-class.md)
- [Elliptical potential lemma](../multi-armed-bandits/linear-bandits/elliptical-potential-lemma.md)
- [Azuma's inequality](../../../../Probability/concentration-inequalities/azuma-inequality.md)

## Expansion

On a good event, built from the uniform self-normalized bound with the covering number of the LSVI-UCB value class, the regression error satisfies $\langle \phi, w^k_h \rangle - Q^\pi_h = \mathbb{P}_h(V^k_{h+1} - V^\pi_{h+1}) + \Delta^k_h$ with $|\Delta^k_h| \le \beta \lVert \phi \rVert_{(\Lambda^k_h)^{-1}}$ for every policy $\pi$; this uses the linearity and the weight bound $2H\sqrt d$ of true action values. Induction backwards in $h$ gives optimism $Q^k_h \ge Q^\star_h$, and then the recursion $\delta^k_h \le \delta^k_{h+1} + \zeta^k_{h+1} + 2\beta \lVert \phi^k_h \rVert_{(\Lambda^k_h)^{-1}}$ for $\delta^k_h = V^k_h(x^k_h) - V^{\pi_k}_h(x^k_h)$. Summing, the martingale differences $\zeta^k_h$, bounded by $2H$, contribute $O(H\sqrt{T\iota})$ by Azuma–Hoeffding, and the bonuses contribute $\beta \sum_h \sqrt{K \sum_k \lVert \phi^k_h \rVert^2_{(\Lambda^k_h)^{-1}}} \le \beta H \sqrt{2dK\iota}$ by Cauchy–Schwarz and the elliptical potential lemma (applicable because $\lVert\phi\rVert \le 1$ and $\lambda = 1$ make each term at most $1$). With $\beta = c\,dH\sqrt\iota$ this is $O(\sqrt{d^3H^3T\iota^2})$.

A complete expansion adds pages for the ridge-regression decomposition of the value-targeted least-squares error (Lemma B.4), the covering number of the LSVI-UCB value class (Lemmas D.5–D.6, via an $\varepsilon$-cover of a Euclidean ball of radius $R$ of size at most $(1+2R/\varepsilon)^d$), and the optimism induction (Lemma B.5).

## Sources

- C. Jin, Z. Yang, Z. Wang and M. I. Jordan, "Provably Efficient Reinforcement Learning with Linear Function Approximation", Conference on Learning Theory (COLT 2020), PMLR 125; journal version Mathematics of Operations Research 48(3):1496–1521, 2023, doi:10.1287/moor.2022.1309. Numbers from arXiv:1907.05388v2: Section 2 (regret), Theorem 3.1 and the remarks after it (space and running time), Section 5 (lower bound discussion), Appendix B (Lemmas B.1–B.6 and the proof of Theorem 3.1). <https://arxiv.org/abs/1907.05388v2>
- A. Agarwal, S. Kakade, A. Krishnamurthy and W. Sun, "FLAMBE: Structural Complexity and Representation Learning of Low Rank MDPs", Advances in Neural Information Processing Systems 33 (NeurIPS 2020). Numbers from arXiv:2006.10814v2: Definition 1 and its footnote (integrated normalization), Lemma 15 and its proof (LSVI-UCB applied under that normalization). <https://arxiv.org/abs/2006.10814v2>
