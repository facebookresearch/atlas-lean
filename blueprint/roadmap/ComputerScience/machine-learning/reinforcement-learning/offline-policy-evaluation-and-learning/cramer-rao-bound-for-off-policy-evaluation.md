# Cramér–Rao bound for off-policy evaluation in tree MDPs

In a discrete tree MDP, where the state is the whole history, every unbiased estimator of a target policy's value from one behavior-policy trajectory has variance at least $\sum_{t=1}^{H+1}\mathbb E\big[\rho_{1:t-1}^{2}\,\mathbb V_t[V(s_t)]\big]$; at each parameter $\theta_0$ the bound is attained by the doubly robust estimator whose model is fixed to the action values under $\theta_0$.

**Discrete tree MDP (Jiang and Li, Definition 1).** Observations $o$ and actions $a$ range over finite sets. The state at step $t$ is the history $s_t=h_t=o_1a_1\cdots o_{t-1}a_{t-1}o_t$. An initial state is $s_1=o_1$, drawn with probability $\mu(o_1)$, and from $s=h$ the action $a$ leads only to states $s'=hao$, with probability $P(o\mid h,a)$. The discount is $\gamma=1$ and rewards are zero except at the end: a final observation $o_{H+1}$ encodes the reward randomness, so the reward $R(h_{H+1})$ is a deterministic function of the full history. The MDP is thus parameterized by the transition probabilities alone, $\theta=\big(P(o\mid h,a)\big)$ with $\mu(o)$ read as $P(o\mid\emptyset)$, subject to $\sum_o P(o\mid h,a)=1$ for every $(h,a)$.

Fix a behavior policy $\pi_0$ and a target policy $\pi_1$, with per-step ratios $\rho_t=\pi_1(a_t\mid s_t)/\pi_0(a_t\mid s_t)$, cumulative ratios $\rho_{1:t}=\prod_{t'\le t}\rho_{t'}$ and $\rho_{1:0}=1$. Let $V(s_t)$ be the value of $\pi_1$ from $s_t$ with the remaining $H+1-t$ steps, so that $V(s_{H+1})=R(h_{H+1})$ and $v^{\pi_1,H}=\mathbb E_{s_1\sim\mu}V(s_1)$. Expectations are over one trajectory $h_{H+1}$ drawn with $\pi_0$, and $\mathbb V_t$ is the variance conditional on $o_1,a_1,\ldots,o_{t-1},a_{t-1}$. The transition probabilities are positive, and the behavior policy is soft, $\pi_0(a\mid h)>0$ for every history $h$ and action $a$, so that every ratio is defined and every parameterized row $(h,a)$ has positive probability $P_0(ha)$ of being reached and followed by $a$ under $\pi_0$. The source's proof divides by $P_0(ha)$; a row that $\pi_0$ never reached would carry no Fisher information.

**Theorem (Jiang and Li, Theorem 2).** For discrete tree MDPs, the variance of any estimator of $v^{\pi_1,H}$ computed from one trajectory of $\pi_0$ that is unbiased for every value of the parameters $\theta$ is at least

$$
\sum_{t=1}^{H+1}\mathbb E\Big[\rho_{1:(t-1)}^{2}\;\mathbb V_t\big[V(s_t)\big]\Big].
$$

The bound is the constrained Cramér–Rao bound for the parameterization $\theta$; it uses no knowledge beyond the discreteness of decisions and outcomes, in particular not the Markov property of a smaller state. Jiang and Li observe (Observation 1) that the [doubly robust estimator](doubly-robust-estimator-is-unbiased.md) with $\widehat Q=Q$ has exactly this variance in a discrete tree MDP, so the state-transition part of its variance cannot be removed by any unbiased estimator without further assumptions. Those action values depend on the unknown parameters. Fixed in advance to the action values under one parameter $\theta_0$, the doubly robust estimate uses only the trajectory, remains unbiased for every $\theta$, and has variance equal to the bound at $\theta=\theta_0$. In a layered acyclic MDP, where different histories may reach the same state, the same bound holds with $\rho_{1:t-1}$ replaced by the ratio of the two policies' marginal state-action probabilities (their Theorem 3).

## Depends on

- [Importance-sampling estimators for off-policy evaluation](importance-sampling-estimators-for-off-policy.md)

## Proof depends on

- [Cramér–Rao inequality for a real estimand of a vector parameter](../../../../Probability/statistical-estimation/fisher-information-and-the-cram-r-rao-bound/cramer-rao-multiparameter.md)

## Expansion

The normalization constraints $F\theta=\mathbf 1$ are affine, so the feasible parameters near $\theta$ are exactly $\theta+U\alpha$ for $\alpha$ near $0$, where the columns of $U$ form an orthonormal basis of the null space of $F$. In the free coordinates $\alpha$ the trajectory law is a smooth family on a finite sample space, the Fisher information is $U^{\top}IU$, positive definite under the positivity hypotheses, and the gradient of the estimand is $U^{\top}K^{\top}$; the multiparameter Cramér–Rao inequality then gives the constrained bound $KU(U^{\top}IU)^{-1}U^{\top}K^{\top}$, which is the form Jiang and Li take from Moore (2010). Index matrices by histories. The Fisher information of one trajectory, whose likelihood under $\pi_0$ is $\mu(o_1)\pi_0(a_1\mid o_1)P(o_2\mid o_1,a_1)\cdots P(o_{H+1}\mid h_H,a_H)$, has entries $I_{hao,h'a'o'}=P_0(ha)/P(o'\mid h',a')$ when $h'a'o'$ is a prefix of $hao$, where $P_0$ is the probability of a prefix under $\pi_0$. Adding terms that vanish on the null space of the constraint Jacobian replaces $I$ by a diagonal matrix, so the constrained inverse is block diagonal, each block $1/P_0(ha)$ times the multinomial bound $\operatorname{diag}(p)-pp^{\top}$ for $p=P(\cdot\mid h,a)$. The gradient of $v^{\pi_1,H}$ has entries $P_1(ha)V(hao)$, with $P_1$ the prefix probability under $\pi_1$. The constrained bound $KU(U^{\top}IU)^{-1}U^{\top}K^{\top}$ becomes $\sum_{ha}\frac{P_1(ha)^2}{P_0(ha)}\operatorname{Var}\big(V(hao)\mid h,a\big)$, and $P_1(ha)/P_0(ha)$ is the cumulative ratio.

## Sources

- N. Jiang and L. Li, *Doubly Robust Off-policy Value Evaluation for Reinforcement Learning*, Proceedings of the 33rd International Conference on Machine Learning, PMLR 48:652–661 (2016). [arXiv:1511.03722v3](https://arxiv.org/abs/1511.03722v3), §5, Definition 1, Theorem 2 with Eq. (13), Observation 1 and the proof of Theorem 2; Appendix C, Definition 2 and Theorem 3 (acyclic case).
- T. J. Moore, *A Theory of Cramér–Rao Bounds for Constrained Parametric Models*, PhD thesis, University of Maryland, College Park (2010), Eq. (3.3) and Corollary 3.10, as cited by Jiang and Li.
