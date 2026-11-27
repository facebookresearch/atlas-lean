# Linear realizability and feature coverage do not suffice for offline evaluation

Even when every policy's action-value function is linear in known $d$-dimensional features and every data distribution has the best possible feature covariance, any offline evaluation algorithm needs $\Omega((d/2)^H)$ samples on some deterministic-transition MDP of horizon $H$ to estimate a policy's value to constant accuracy.

**Setting.** An episodic MDP $M=(S,A,P,R,H)$ has a fixed initial state $s_1$, state levels $S_1,\ldots,S_H\subseteq S$ that are pairwise disjoint, transitions $P(\cdot\mid s,a)$ from level $h$ to level $h+1$, reward distributions $R(s,a)$, and rewards $r_h\in[-1,1]$ almost surely. A stochastic policy $\pi$ chooses $a_h\sim\pi(\cdot\mid s_h)$, with action values $Q^\pi_h(s,a)=\mathbb E[\sum_{h'=h}^{H}r_{h'}\mid s_h=s,a_h=a,\pi]$ and value $V^\pi=\mathbb E[\sum_{h=1}^{H}r_h\mid s_1,\pi]$. The learner is given a policy $\pi$, a feature map $\phi:S\times A\to\mathbb R^{d}$, and for each level $h$ a dataset $D_h$ of independent tuples $(s,a,r,s')$ with $(s,a)\sim\mu_h\in\Delta(S_h\times A)$, $r\sim R(s,a)$ and $s'\sim P(\cdot\mid s,a)$; it must output an estimate of $V^\pi$.

- *Realizability (Assumption 1).* For every policy $\pi$ there are $\theta^\pi_1,\ldots,\theta^\pi_H\in\mathbb R^{d}$ with $Q^\pi_h(s,a)=(\theta^\pi_h)^{\top}\phi(s,a)$ for all $h$ and $(s,a)$.
- *Feature coverage (Assumption 2).* $\|\phi(s,a)\|_2\le 1$ for all $(s,a)$, and for every $h$ the smallest eigenvalue of $\mathbb E_{(s,a)\sim\mu_h}[\phi(s,a)\phi(s,a)^{\top}]$ equals $1/d$, the largest value that $\|\phi\|_2\le1$ allows.

**Theorem (Wang, Foster and Kakade, Theorem 4.1).** Suppose Assumption 2 holds, and fix an algorithm that takes a policy and a feature map as input. There is an MDP with deterministic transitions satisfying Assumption 1 such that, for any policy $\pi$, the algorithm needs $\Omega\big((d/2)^{H}\big)$ samples to output $V^\pi$ up to a constant additive error with probability at least $0.9$.

The construction takes $d$ even and two actions; its rewards are random only at the last level. For $H=1$ the two assumptions make ordinary least squares accurate with $O(d)$ samples, so the barrier is the horizon: errors are amplified by a factor $\sqrt{d/2}$ per level. Adding a first action that ends the episode with a fixed reward turns the result into the same lower bound for finding a near-optimal policy offline. Here realizability holds for all policies and coverage is spectral; compare the tabular coverage notions of the [concentrability coefficient over admissible distributions](concentrability-over-admissible-distributions.md).

## Depends on

- [Stochastic policy](../stochastic-policies-and-discounted-occupancy/stochastic-policy.md)
- [Markov decision process](../../../heuristic-search-and-planning/value-iteration/mdp.md)

## Proof depends on

- [Le Cam's bound in KL form](../../../../Probability/statistical-estimation/minimax-lower-bounds/lecam-kl.md)
- [Tensorization of KL divergence and product Pinsker bounds](../../../../InformationTheory/information-inequalities/kl-tensorization-and-product-conditioning/kl-tensorization-for-products.md)

## Expansion

Let $\hat d=d/2$. Each level has states $s^1_h,\ldots,s^{\hat d}_h$ and an extra state $s^{\hat d+1}_h$; action $a_1$ moves to the extra state of the next level and $a_2$ from $s^c_h$ to $s^c_{h+1}$. The features are $\phi(s^c_h,a_1)=e_c$, $\phi(s^c_h,a_2)=e_{c+\hat d}$ and $\phi(s^{\hat d+1}_h,a)=\hat d^{-1/2}\sum_{c\le\hat d}e_c$, and the data distributions are uniform on the pairs $(s^c_h,a)$, $c\le\hat d$, which gives covariance $I/d$. The rewards at the last level are $\pm1$ with mean $r_0$, and the rewards at the extra states are chosen so that $Q$ is linear for every policy, with the value at the extra state of level $1$ equal to $r_0\hat d^{H/2}$. The extra states never appear in the data, so estimating $V^\pi$ to constant error requires distinguishing $r_0=0$ from $r_0=\hat d^{-H/2}$ from last-level rewards, which needs $\Omega(\hat d^{H})$ samples. The source cites a two-coin testing lower bound (Anthony and Bartlett, Lemma 5.1) for this step; the same count follows from Le Cam's two-point bound in KL form and tensorization: the data from all other state-action pairs have the same law under both hypotheses, the divergence between the two $\pm1$ reward laws is $O(\hat d^{-H})$, so $n$ last-level samples have divergence $O(n\hat d^{-H})$, and two error probabilities of at most $0.1$ each force it to be bounded below by a constant.

## Sources

- R. Wang, D. P. Foster and S. M. Kakade, *What are the Statistical Limits of Offline RL with Linear Function Approximation?*, International Conference on Learning Representations (ICLR 2021). [arXiv:2010.11895v1](https://arxiv.org/abs/2010.11895v1), §3 (setting, Assumption 1), §4 (Assumption 2, Theorem 4.1 and the reduction to policy optimization) and §4.1 (construction); Assumptions 1–2 and Theorem 4.1 carry the same numbers in the [conference version](https://par.nsf.gov/servlets/purl/10276113), where the construction follows Theorem 4.1 within §4 instead of a separate §4.1.
