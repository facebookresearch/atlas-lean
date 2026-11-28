# FLAMBE learns low-rank MDP models

Under realizability of both embeddings, FLAMBE learns, with probability $1-\delta$, a model of a low-rank MDP of dimension $d$ that is $\varepsilon$-accurate in total variation on the state-action distribution of every policy at every step. It uses $\tilde O(H^{22}K^9d^7\log(|\Phi||\Upsilon|/\delta)/\varepsilon^{10})$ trajectories and runs in polynomial time given maximum-likelihood and sampling oracles.

**Setting.** $M$ is a [low-rank MDP](low-rank-mdp.md) of dimension $d$ and horizon $H$ with $K$ actions, and the finite classes $\Phi, \Upsilon$ contain $\phi^\star_h$ and $\mu^\star_h$ for every $h$ (Assumption 1). Each candidate pair $(\phi,\mu) \in \Phi\times\Upsilon$ satisfies the normalization of Definition 1: $\lVert\phi(x,a)\rVert_2\le1$ for every $(x,a)$ and $\lVert\int\mu(x)g(x)\,dx\rVert_2\le\sqrt d$ for every $g:\mathcal X\to[0,1]$. It is used as a transition kernel $\langle\phi(x,a),\mu(\cdot)\rangle$: the maximum-likelihood oracle treats it as a conditional density and the sampling oracle draws from it. The goal is reward-free system identification: output $\hat M = (\hat\phi_{0:H-1}, \hat\mu_{0:H-1})$ satisfying condition (1) of the source, with $\lVert\cdot\rVert_{\mathrm{TV}}$ the total variation distance:

$$
\mathbb{E}\Big[\big\lVert \langle \hat\phi_h(x_h,a_h), \hat\mu_h(\cdot)\rangle - T_h(\cdot \mid x_h,a_h) \big\rVert_{\mathrm{TV}} \,\Big|\, \pi, M\Big] \le \varepsilon \qquad \text{for all policies } \pi \text{ and all } h.
$$

**Oracles.** MLE: given triples $(x,a,x')$, return $\arg\max_{\phi\in\Phi,\mu\in\Upsilon}\sum \log\langle\phi(x,a),\mu(x')\rangle$. SAMP: given $(\phi,\mu) \in \Phi\times\Upsilon$ and $(x,a)$, return an independent sample $x' \sim \langle\phi(x,a),\mu(\cdot)\rangle$.

**Algorithm.** Start from the uniformly random policy. In iteration $j$, for each $h$: roll in with the current exploratory policy, take a uniform action at step $h$, add $n$ transitions to the dataset, and refit $(\hat\phi_h,\hat\mu_h)$ by MLE on all data so far. Then, in the learned model, run an elliptical planner for each step. It repeatedly finds a policy maximizing $\mathbb{E}[\hat\phi^{\mathsf T}\Sigma^{-1}\hat\phi]$ and adds its feature covariance to $\Sigma$, until the maximum is at most $\beta$. The next exploratory policy is the uniform mixture of the discovered policies, each followed by random actions. Output the final model.

**Theorem.** Fix $\varepsilon \in (0,1)$ and $\delta \in (0,1)$. If $M$ is a low-rank MDP with dimension $d$ and horizon $H$ and Assumption 1 holds, then FLAMBE with the elliptical planner and appropriate $\beta$, $J_{\max}$ and $n$ computes a model $\hat M$ satisfying condition (1) with probability at least $1-\delta$. It collects in total

$$
\tilde O\Big(\frac{H^{22}K^9d^7\log(|\Phi||\Upsilon|/\delta)}{\varepsilon^{10}}\Big)
$$

trajectories and runs in polynomial time with polynomially many calls to MLE and SAMP.

**Scope.** This is a representation-learning result: the features are learned, not given, and the guarantee covers every reward function afterwards, since accurate one-step models let linear methods in $\hat\phi$ fit backups of any $[0,1]$-valued function on every policy's distribution (Lemma 1). No reachability assumption is needed. The bound scales with the number of actions $K$, unlike linear-MDP bounds with known features. Computational efficiency is relative to the two oracles. The source proves a sharper $\tilde O(H^{11}K^5d_{LV}^5\log(|\Phi||\Upsilon|/\delta)/\varepsilon^3)$ (Theorem 3) under stronger hypotheses: $M$ admits a simplex factorization with embedding dimension $d_{LV}$, Assumption 1 holds, every $\phi \in \Phi$ (not only the true one) takes values in the simplex $\Delta([d_{LV}])$ at every $(x,a)$, and the planner is the source's Algorithm 3 instead of the elliptical planner. In the same setting with the reachability Assumption 2 (every latent variable reachable with probability at least $\eta_{\min} > 0$), a version that plans with real trajectories avoids SAMP and collects $\mathrm{poly}(d_{LV},H,K,1/\eta_{\min},1/\varepsilon,\log(|\Phi||\Upsilon|/\delta))$ trajectories with $H$ calls to MLE (Theorem 4).

## Depends on

- [Low-rank MDP](low-rank-mdp.md)
- [Total variation distance between finite measures](../../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Proof depends on

- [Regret of LSVI-UCB in linear MDPs](regret-of-lsvi-ucb-in-linear-mdps.md)
- [Two-sided Hoeffding inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-abs-avg-sub-ge-le.md)

## Expansion

The source names three steps. First, MLE over $\Phi\times\Upsilon$ is shown to converge in Hellinger and total-variation distance on the data distribution of the exploratory policies, using results from the statistics literature because the log-likelihood is unbounded. Second, a simulation lemma transfers this error to any policy $\pi$. It uses the low rank of $T_h$ to bound $\pi$'s model error by the exploratory error plus the probability that $\pi$ visits true features $\phi^\star_{h-1}$ with large $\phi^{\star\mathsf T}_{h-1}\Sigma_{h-1}^{-1}\phi^\star_{h-1}$, where $\Sigma_{h-1}$ is the exploratory second-moment matrix. Third, since $\phi^\star$ is unknown, the planner instead makes the covariance of the learned features $\hat\phi_{h-2}$ well conditioned and appends a random action. Either it explores a new direction or no policy makes the quantity large, which certifies condition (1). An elliptical potential argument bounds the number of exploring iterations. The planner's optimization over all policies in the learned model is solved by running LSVI-UCB there through the sampling oracle, with the learned features as known features; its regret guarantee makes one of the iterates near-optimal, and Monte Carlo rollouts of each iterate pick one out (the proof of Lemma 15). Only a polynomial guarantee is needed for this step.

A complete expansion adds pages for the maximum-likelihood total-variation bound over a finite class of conditional densities (Theorem 21), the simulation lemma for low-rank models (Lemma 6), and the elliptical potential lemma for sums of positive semidefinite matrices (Lemma 26). Fix $d\ge1$ and $\lambda>0$. For positive semidefinite $d\times d$ matrices $X_1, \dots, X_T$ with $\mathrm{tr}(X_t) \le 1$ and $M_t = \lambda I + \sum_{s \le t} X_s$, the form to plan is $\sum_{t} \mathrm{tr}(X_t M_{t-1}^{-1}) \le (1 + 1/\lambda)\, d \log(1 + T/(d\lambda))$. The source prints $\log(1 + T/d)$; its proof drops the initial term $-d\log\lambda$, which is nonnegative when $\lambda \le 1$, so its argument establishes the shorter bound for $\lambda \ge 1$, but the shorter bound fails for some small positive $\lambda$ (with $d = T = 1$, $X_1 = 1$ and $\lambda = 1/100$ the left side is $100$ and the printed bound about $70$). Keeping the initial determinant term changes the outer-iteration bound only by a logarithmic factor; the stated $\tilde O$ sample bound and polynomial-time guarantee are unchanged.

## Sources

- A. Agarwal, S. Kakade, A. Krishnamurthy and W. Sun, "FLAMBE: Structural Complexity and Representation Learning of Low Rank MDPs", Advances in Neural Information Processing Systems 33 (NeurIPS 2020). Numbers from arXiv:2006.10814v2: Eq. (1), Lemma 1, Definition 3 (oracles), Algorithms 1–3, Theorems 2–4, Assumption 2, Section 5.2 (the paragraph "Challenges in the analysis"), Lemma 6, Lemma 15, Theorem 21 (MLE guarantee), Lemma 26 (elliptical potential for matrices). <https://arxiv.org/abs/2006.10814v2>
