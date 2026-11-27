# Witness rank

The witness rank of a model class is the smallest rank of a matrix that is sandwiched between scaled average Bellman errors and witnessed model misfits, the latter being integral-probability-metric discrepancies between a candidate model's predictions and the true dynamics under another model's policy.

**Setting.** A finite-horizon contextual decision process has a context space $\mathcal{X}$ partitioned into $\mathcal{X}_1, \dots, \mathcal{X}_{H+1}$, $K = |\mathcal{A}|$ actions, an initial distribution $P_0$ on $\mathcal{X}_1$, transitions $P_{x,a} \in \Delta(\mathcal{X}_{h+1})$ for $x \in \mathcal{X}_h$, and reward distributions $R(x,a)$ on $[0,1]$ with $\sum_{h=1}^H r_h \le 1$ almost surely. A model $M = (R, P)$ shares $\mathcal{X}$ and $\mathcal{A}$; $\pi_M$, $Q_M$, $V_M$ and $v_M$ are its optimal policy, action-value, value and initial value, computed in $M$. The true model is $M^\star$, and "$x_h \sim \pi$" means $x_h$ is reached by running $\pi$ in $M^\star$ for $h-1$ steps.

**Witnessed model misfit.** For a class $\mathcal{F}$ of functions $\mathcal{X}\times\mathcal{A}\times\mathbb{R}\times\mathcal{X} \to \mathbb{R}$, models $M, M'$ and a step $h$,

$$
\mathcal{W}(M, M', h; \mathcal{F}) = \sup_{f\in\mathcal{F}} \mathbb{E}_{x_h \sim \pi_M,\ a_h \sim \pi_{M'}} \Big[ \mathbb{E}_{(r,x') \sim M'_h} f(x_h,a_h,r,x') - \mathbb{E}_{(r,x') \sim M^\star_h} f(x_h,a_h,r,x') \Big].
$$

That is, one test function $f$ is chosen for all contexts: $\mathcal{W}$ is the IPM between two joint laws of $(x_h, a_h, r, x')$ that share the marginal of $(x_h,a_h)$ (contexts from $\pi_M$ and actions from $\pi_{M'}$ in the true environment) and have conditionals $M'_h$ and $M^\star_h$. It is not the average of per-context IPMs, which can be larger. When $\mathcal{F} = \{\lVert f\rVert_\infty \le 1\}$ is the class of all measurable test functions bounded by $1$, a test function can be chosen separately at each $(x_h,a_h)$, the two coincide, and $\mathcal{W}$ is an averaged total variation distance between $M'$ and $M^\star$ (the source's Eq. (3)), in the source's convention $\lVert P_1 - P_2\rVert_{\mathrm{TV}} = \sum_x |P_1(x) - P_2(x)|$ (twice the usual one).

**Average Bellman error.** $\mathcal{E}_B(M, M', h) = \mathbb{E}\big[Q_{M'}(x_h,a_h) - r_h - Q_{M'}(x_{h+1},a_{h+1}) \mid x_h \sim \pi_M,\ a_{h:h+1} \sim \pi_{M'}\big]$ in the true environment.

**Bellman domination (Assumption 2).** $\mathcal{F}$ is symmetric ($f \in \mathcal{F} \Rightarrow -f \in \mathcal{F}$), finite, $\lVert f\rVert_\infty \le 2$, and $\mathcal{W}(M,M',h;\mathcal{F}) \ge \mathcal{E}_B(M,M',h)$ for all $M, M' \in \mathcal{M}$. A sufficient condition is that $\mathcal{F}$ contains the functions $r + V_M(x')$ for $M \in \mathcal{M}$.

**Definition.** For $\beta > 0$ and $B \in \mathbb{R}^{n\times n}$, $\mathrm{rank}(B,\beta)$ is the least nonnegative integer $k$ with $B = UV^{\mathsf T}$, $U, V \in \mathbb{R}^{n\times k}$ and $\lVert u_i\rVert_2\lVert v_j\rVert_2 \le \beta$ for all rows, and $+\infty$ if no such factorization exists (for example $B = [2]$ and $\beta = 1$, since $|u_1^{\mathsf T}v_1| \le \lVert u_1\rVert_2\lVert v_1\rVert_2$). The source says "smallest integer" and leaves the infeasible case implicit; the value $+\infty$ is this page's convention. For a finite model class $\mathcal{M}$, test functions $\mathcal{F}$, $\kappa \in (0,1]$ and $h \in [H]$, let $\mathcal{N}_{\kappa,h}$ be the set of matrices $A \in \mathbb{R}^{|\mathcal{M}|\times|\mathcal{M}|}$ with

$$
\kappa\, \mathcal{E}_B(M, M', h) \le A(M, M') \le \mathcal{W}(M, M', h) \qquad \text{for all } M, M' \in \mathcal{M}.
$$

The witness rank is $\mathrm{W}(\kappa, \beta, \mathcal{M}, \mathcal{F}, h) = \min_{A \in \mathcal{N}_{\kappa,h}} \mathrm{rank}(A, \beta) \in \mathbb{Z}_{\ge 0} \cup \{+\infty\}$, and $\mathrm{W}_\kappa = \max_{h\in[H]} \mathrm{W}(\kappa,\beta,\mathcal{M},\mathcal{F},h)$. Under Bellman domination with a symmetric $\mathcal{F}$ the set $\mathcal{N}_{\kappa,h}$ contains $\mathcal{W}$ itself (as $\mathcal{W} \ge 0$ and $\mathcal{W} \ge \mathcal{E}_B$), so the minimum is over a nonempty set and is attained.

## Depends on

- [Probability measure](../../../../Probability/foundations/probability-measures/is-probability-measure.md)

## Proof depends on

None.

## Expansion

Taking $A = \kappa\mathcal{E}_B$ shows that the witness rank never exceeds the rank of the scaled average Bellman error matrix; the source records that it can be much smaller, as for factored MDPs with a suitable $\mathcal{F}$. At the other extreme $A = \mathcal{W}$: its rank counts how many context distributions suffice to witness the misfit of every wrong model. Without some such structure, realizability and Bellman domination alone allow a lower bound of order $K^{H-1}$ episodes (the source's Proposition 4). The dependence on $\beta$ is logarithmic in the sample-complexity bounds.

## Sources

- W. Sun, N. Jiang, A. Krishnamurthy, A. Agarwal and J. Langford, "Model-based RL in Contextual Decision Processes: PAC bounds and Exponential Improvements over Model-free Approaches", Conference on Learning Theory (COLT 2019), PMLR 99:2898–2933. Numbers from arXiv:1811.08540v3: Section 2.1 (CDPs), Section 2.2 (model class, Assumption 1), Definition 3 with Eqs. (2)–(4), Assumption 2, Proposition 4, Definition 5. <https://arxiv.org/abs/1811.08540v3>
