# Regret lower bound for linear mixture MDPs

For every algorithm there is an inhomogeneous episodic $B$-bounded linear mixture MDP on which its expected regret over $K$ episodes is $\Omega(dH\sqrt T)$, $T = KH$, provided $B > 1$, $d \ge 4$, $H \ge 3$ and $K \ge \max\{(d-1)^2H/2,\ (d-1)/(32H(B-1))\}$.

**Statement.** Let $B > 1$, $d \ge 4$, $H \ge 3$ and

$$
K \ge \max\Big\{\frac{(d-1)^2 H}{2},\ \frac{d-1}{32H(B-1)}\Big\}.
$$

Then for any algorithm there is an inhomogeneous, episodic, $B$-bounded [linear mixture MDP](linear-mixture-mdp.md) $M_\Theta$, $\Theta = (\theta_1,\dots,\theta_H)$, with feature dimension $d$ and horizon $H$, such that

$$
\mathbb{E}_\Theta\big[\mathrm{Regret}(M_\Theta, K)\big] = \Omega\big(dH\sqrt{T}\big), \qquad T = KH,
$$

where $\mathbb{E}_\Theta$ is the expectation under the interconnection of the algorithm and $M_\Theta$ and the regret is $\sum_k [V^\ast_1(s^k_1) - V^{\pi^k}_1(s^k_1)]$.

**Instance.** States $x_1, \dots, x_{H+2}$ with $x_{H+1}, x_{H+2}$ absorbing, actions $\mathcal{A} = \{-1,1\}^{d-1}$, start state $x_1$, reward only on transitions out of $x_{H+2}$. Under action $a$ at stage $h$ from $x_i$, $i \le H$, the next state is $x_{H+2}$ with probability $\delta + \langle\mu_h, a\rangle$ and $x_{i+1}$ otherwise, where $\delta = 1/H$ and $\mu_h \in \{-\Delta, \Delta\}^{d-1}$ with $\Delta = \sqrt{\delta/K}/(4\sqrt2)$. This is a linear mixture MDP with explicit $\phi$ and $\theta_h = (1/\alpha, \mu_h^{\mathsf T}/\beta)^{\mathsf T}$, $\alpha = \sqrt{1/(1+\Delta(d-1))}$, $\beta = \sqrt{\Delta/(1+\Delta(d-1))}$. The admissibility condition $\lVert\phi_V\rVert_2 \le 1$ holds for $V$ with values in $[0,1]$, and the condition on $K$ gives $\lVert\theta_h\rVert_2 \le B$.

Together with the [regret of UCRL-VTR+](regret-of-ucrl-vtr-plus.md), this shows that the rate $dH\sqrt T$ is attained up to logarithmic factors in the regime $d \ge H$, $T \ge d^4H^2 + d^3H^3$.

## Depends on

- [Linear mixture MDP](linear-mixture-mdp.md)

## Proof depends on

- [Pinsker's inequality for probability measures](../../../../InformationTheory/information-inequalities/total-variation-and-pinsker-s-inequality/of-real-two-mul-total-variation-dist-sq.md)
- [Divergence decomposition for stochastic bandits](../multi-armed-bandits/divergence-decomposition-for-stochastic-bandits.md)

## Expansion

From $x_h$ the optimal action maximizes $\langle \mu_h, a\rangle$, so each of the first $\Omega(H)$ stages is a linear bandit on the hypercube with Bernoulli payoffs of mean $\delta + \langle\mu_h,a\rangle$ and payoff scale $\Omega(H)$. Because $(1-\delta)^{H/2}$ is bounded below, every such stage is reached with constant probability even under the optimal policy. The standard hypercube argument for linear bandits flips one coordinate of $\mu_h$ at a time and compares the two laws. It uses Pinsker's inequality and the divergence decomposition of the history law over rounds (arms $\{-1,1\}^{d-1}$, Bernoulli rewards), with $\mathrm{KL}(\mathrm{B}(a),\mathrm{B}(b)) \le 2(a-b)^2/a$ for $a \le 1/2$ and $a + b \le 1$. It gives regret $\Omega(dH\sqrt{K\delta})$ per stage; summing over $\Omega(H)$ stages and using $\delta = 1/H$ gives $\Omega(dH\sqrt{KH}) = \Omega(dH\sqrt T)$.

A complete expansion adds pages for the Bernoulli relative-entropy bound $\mathrm{KL}(\mathrm{B}(a),\mathrm{B}(b)) \le 2(a-b)^2/a$ for $a \le 1/2$, $a + b \le 1$, and for the hypercube linear-bandit lower bound used per stage (the source's Lemma C.8), together with the reduction from the MDP to the stagewise bandit problems (Lemma C.7).

## Sources

- D. Zhou, Q. Gu and Cs. Szepesvári, "Nearly Minimax Optimal Reinforcement Learning for Linear Mixture Markov Decision Processes", Conference on Learning Theory (COLT 2021), PMLR 134:4532–4576. Numbers from arXiv:2012.08507v2: Theorem 5.6 with its proof sketch, Figure 1, Eq. (5.12), Remark 5.7, Appendix C.3 (Lemmas C.7–C.8, Eq. (C.29)). <https://arxiv.org/abs/2012.08507v2>
