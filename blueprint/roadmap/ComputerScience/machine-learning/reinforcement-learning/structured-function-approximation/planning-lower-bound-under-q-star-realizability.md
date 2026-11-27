# Planning lower bound under linear realizability of the optimal action values

Knowing features that make $q^\star$ exactly linear does not make planning with a generative model query-efficient. Any planner that is $9/128$-sound on all $q^\star$-realizable $H$-horizon problems with $d$-dimensional features needs $\min(e^{\Omega(d)}, \Omega(2^H))$ queries in the worst case.

**Problem class.** An MDP $M = (\mathcal{S}, \mathcal{A}, Q)$ has a finite action set and kernels $Q_a(\cdot \mid s)$ giving a reward and a next state; $\mathcal{S}_h$ is the set of states reachable from the fixed initial state $s_1$ in $h-1$ steps. A feature map $\varphi = (\varphi_h)_{h\in[H]}$, $\varphi_h : \mathcal{S}\times\mathcal{A} \to \mathbb{R}^d$, may depend on the stage. The pair $(M,\varphi)$ is *$q^\star$-realizable* if there is $\theta^\star \in \mathbb{R}^d$ with

$$
q^\star_h(s,a) = \langle \varphi_h(s,a), \theta^\star \rangle \qquad \text{for all } h \in [H],\ (s,a) \in \mathcal{S}_h \times \mathcal{A}.
$$

$\mathcal{M}_{H,d}$ is the set of such pairs with horizon $H$, dimension $d$ and rewards in $[0,1]$ almost surely. No bound on $\lVert\varphi\rVert$ or $\lVert\theta^\star\rVert$ is imposed, and only $q^\star$ (not the transitions, nor other policies' values) is assumed linear.

**Planners.** A local planner receives a stage $h$, a state $s_{\mathrm{in}} \in \mathcal{S}_h$, the state sets, the actions and the feature map. It sends queries $(s,a)$ to a simulator returning $(R, S') \sim Q_a(\cdot \mid s)$, may randomize, stops after $N < \infty$ queries almost surely, and outputs an action. Called along a trajectory, it implements a memoryless policy $\pi$. It is *$\delta$-sound* if $\sup_{h\in[H], s\in\mathcal{S}_h} \big(v^\star_h(s) - v^\pi_h(s)\big) \le \delta$ for every $(M,\varphi) \in \mathcal{M}_{H,d}$. Its query cost is $C(\mathcal{P},H,d) = \sup_{(M,\varphi)\in\mathcal{M}_{H,d}} \sup_{s_{\mathrm{in}},h} \mathbb{E}[N]$.

**Theorem.** For $d$ and $H$ large enough and any $0 < \eta \le \frac12 - \frac{2}{\log_2(d-1)}$, every $\frac{9}{128}$-sound planner satisfies

$$
C(\mathcal{P},H,d) = \Omega\Big(\min\big\{ e^{(d-1)^{2\eta}/8},\ 2^{-H} d^{H(\frac12-\eta)} \big\}\Big).
$$

Choosing $\eta = \frac12 - \frac{2}{\log_2(d-1)}$ gives $C(\mathcal{P},H,d) = \min\big(e^{\Omega(d)}, \Omega(2^H)\big)$. The explicit form of the bound is proved for $d \ge 18$ and $H \ge 1$. In the $\alpha$-discounted setting with $\alpha \ge 2/3$ the same construction gives query complexity $e^{\Omega(d)}$.

**Scope.** This is an information-theoretic bound on queries; it holds for planners with unlimited computation. The hard instances have deterministic transitions, rewards that are deterministic except at the last stage, and a number of actions $k \approx e^{d^{2\eta}/8}$ that grows exponentially; the bound says nothing directly about small action sets. The source also shows that least-squares value iteration with a near-optimal design is $\delta$-sound with $\tilde O(H^5(2d)^{H+1}/\delta^2)$ queries, exponential in $H$.

## Depends on

- [Probability measure](../../../../Probability/foundations/probability-measures/is-probability-measure.md)

## Proof depends on

None.

## Expansion

It suffices to defeat "transition-sound" planners, which at every reachable state play an action with optimality gap at least $\delta$ with probability at most $\zeta$ (the source's Definition 5). For $\delta > 0$ and $\zeta \in (0,1]$, a $\delta$-sound planner is $(\delta/\zeta, \zeta)$-transition-sound (Proposition 6). Conversely, a $(\delta,\zeta)$-transition-sound planner is $(H\delta + H(H+1)\zeta/2)$-sound, a conversion that depends on the horizon. The construction has $k$ MDPs $M_a$ sharing states, actions and features, with $a$ the optimal action everywhere in $M_a$ and an action gap of at least $1/4$ at $s_1$. The features are built from nearly orthogonal unit vectors: the source's Lemma 12 (from Du et al.) gives, for $\gamma > 0$ and $d_0 \ge \lceil 8\log k/\gamma^2 \rceil$, $k$ unit vectors in $\mathbb{R}^{d_0}$ with pairwise $|\langle v_a, v_b\rangle| \le \gamma$, and the constant $8$ there is what appears in the exponent $e^{(d-1)^{2\eta}/8}$. States form a tree of action sequences without repetition, and the optimal action exits to a reward-free chain. This keeps $q^\star$ realizable while the value signal is amplified by a factor of about $d^{1/2-\eta}$ per stage backwards from noisy last-stage rewards. A symmetric test MDP $M_0$ satisfies $\Pr_{M_a}(a \notin A_{1:n}) \ge \frac34 \Pr_{M_0}(a \notin A_{1:n})$. With $n \le k/4$ queries some action is rarely tried under $M_0$, so the planner fails on that $M_a$ unless it uses $\Omega(n)$ queries.

A complete expansion adds pages for that near-orthogonal-vectors lemma with its explicit constant (a Johnson–Lindenstrauss-type statement), for the two conversions between soundness and transition soundness (Proposition 6), and for the comparison of a planner's action frequencies on $M_a$ and on the symmetric test MDP (Eq. (6) and Lemma 11).

## Sources

- G. Weisz, P. Amortila and Cs. Szepesvári, "Exponential Lower Bounds for Planning in MDPs With Linearly-Realizable Optimal Action-Value Functions", Algorithmic Learning Theory (ALT 2021), PMLR 132:1237–1264. Numbers from arXiv:2010.01374v2: Section 2 (MDPs, $\mathcal{S}_h$), Assumptions 1 and 3, Definitions 2, 4, 5 and 7, Proposition 6, Theorem 9, Corollary 10, Lemmas 11–12, Sections 4.8 and 4.9 (proof and discounted case), Propositions 14–15. <https://arxiv.org/abs/2010.01374v2>
