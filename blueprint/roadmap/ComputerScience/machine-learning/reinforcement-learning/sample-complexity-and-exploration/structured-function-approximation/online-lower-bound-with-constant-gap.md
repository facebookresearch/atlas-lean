# Online lower bound for linearly realizable MDPs with a constant gap

In online episodic RL, linear realizability of $Q^\star$ together with a constant minimum suboptimality gap still allows instances where finding a $0.05$-optimal policy with probability above $0.1$ needs $2^{\Omega(\min\{d,H\})}$ samples. Gap assumptions that make generative-model planning easy do not rescue online learning.

**Setting.** An episodic MDP $(\mathcal{S}, \mathcal{A}, H, P, \{R_h\})$ with $|\mathcal{A}| = A$, a stationary transition kernel $P$, reward distributions $R_h$, and an initial distribution $\mu$. In the online setting the agent interacts only through episodes started from $s_1 \sim \mu$; there is no generative model. The agent receives a feature map $\phi : \mathcal{S}\times\mathcal{A} \to \mathbb{R}^d$. The assumptions are:

1. *Realizability*: for every $h \in [H]$ there is $\theta^\ast_h \in \mathbb{R}^d$ with $Q^\ast_h(s,a) = \phi(s,a)^{\mathsf T}\theta^\ast_h$ for all $(s,a)$, with the regularity $\lVert\theta^\ast_h\rVert_2 = O(1)$ and $\lVert\phi(s,a)\rVert_2 = O(1)$.
2. *Minimum gap*: with $\Delta_h(s,a) = V^\ast_h(s) - Q^\ast_h(s,a)$, $\min\{\Delta_h(s,a) : \Delta_h(s,a) > 0\} \ge \Delta_{\min}$.

**Theorem.** There are universal constants $c_0, c_1 > 0$ such that for every online RL algorithm that takes $\phi$ as input, there is an MDP with a feature map satisfying both assumptions with $\Delta_{\min} \ge c_0$ on which the algorithm needs $2^{c_1 \min\{d, H\}}$ samples to output a policy $\pi$ with

$$
\mathbb{E}_{s_1\sim\mu} V^\pi(s_1) \ge \mathbb{E}_{s_1\sim\mu} V^\ast(s_1) - 0.05
$$

with probability greater than $0.1$.

**Scope.** The hard family is a "leaking complete graph" on $m + 1$ states with $m = \lfloor \exp(\gamma^2 d/8) \rfloor$ actions, $\gamma = 1/6$, and features of dimension $d + 1$, a shift that only changes the constants in the exponent. It has a single $\theta^\ast = (1, v(a^\ast))$ for all stages and rewards that can be negative (for example $-1$ at the terminal state for every action other than action $1$). Exponentially many actions are needed in this construction. The assumption constrains $Q^\ast$ only, not the transition model. The source contrasts this with the generative-model setting, where realizability plus a gap admits polynomial sample complexity.

## Depends on

- [Probability measure](../../../../../Probability/foundations/probability-measures/is-probability-measure.md)

## Proof depends on

- [Johnson–Lindenstrauss lemma](../../../../../Geometry/metric-geometry/johnson-lindenstrauss.md)

## Expansion

Choose $m$ nearly orthogonal unit vectors $v(1), \dots, v(m)$ in $\mathbb{R}^d$ with $|\langle v(i), v(j)\rangle| \le \gamma$; the source's Lemma 1 gives them for $m \le \exp(\gamma^2 d/8)$ and attributes it to the Johnson–Lindenstrauss lemma. Applying the Johnson–Lindenstrauss lemma to the standard basis vectors together with the origin, and polarizing, gives such vectors with a worse constant in the exponent, which changes only $c_1$. In $M_{a^\ast}$, from state $a_1$ action $a_2 \ne a^\ast, a_1$ moves to state $a_2$ with probability $\langle v(a_1), v(a_2)\rangle + 2\gamma \in [\gamma, 3\gamma]$ and otherwise to an absorbing terminal state. Action $a^\ast$, or the action naming the current state, moves to the terminal state. Rewards are chosen so that $Q^\ast_h = \langle\phi, (1, v(a^\ast))\rangle$ at every stage with a constant gap. Information about $a^\ast$ is revealed only by playing $a^\ast$ or by reaching a nonterminal state at stage $H$. The first is unlikely among $2^{\Theta(d)}$ actions, and the second is exponentially unlikely in $H$ because every step leaks to the terminal state with probability at least $1 - 3\gamma$. Hence $2^{\Omega(\min\{d,H\})}$ episodes are needed.

A complete expansion adds pages for the near-orthogonal-vectors corollary of the Johnson–Lindenstrauss lemma and for the information argument bounding the probability of taking $a^\star$ or reaching a nonterminal state at stage $H$ (the source's Lemma 4), and for the verification of the constant gap (Lemma 3).

## Sources

- Y. Wang, R. Wang and S. M. Kakade, "An Exponential Lower Bound for Linearly Realizable MDP with Constant Suboptimality Gap", Advances in Neural Information Processing Systems 34 (NeurIPS 2021). Numbers from arXiv:2103.12690v2: Section 3 (setting), Assumptions 1 and 2, Theorem 1, Section 4.1 (construction, Lemma 1, Lemma 2). <https://arxiv.org/abs/2103.12690v2>
