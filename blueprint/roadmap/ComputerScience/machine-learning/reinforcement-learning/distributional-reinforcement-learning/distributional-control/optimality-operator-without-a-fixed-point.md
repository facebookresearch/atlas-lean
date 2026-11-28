# A distributional optimality operator without a fixed point

Some distributional Bellman optimality operators have no fixed point.

There exist a finite MDP with a [reward–transition kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md) whose rewards are bounded, a discount $\gamma \in (0,1)$ and a greedy selection rule whose [distributional Bellman optimality operator](../distributional-control/distributional-bellman-optimality-operator.md) $\mathcal{T}$ has no fixed point in $\mathscr{P}_1(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$.

This discounted existential statement is the form taken here, in the setting of these pages ($\gamma < 1$, no terminal actions); it is derived below and is not stated in this form by the source. Bellemare, Dabney and Munos state the general phenomenon, that not all distributional optimality operators have a fixed point, with an undiscounted witness that uses terminal actions, outside this setting: two states, a single transition from $x_1$ to $x_2$, at $x_2$ action $a_1$ with reward $0$ and action $a_2$ with reward $1$ or $-1$ with probability $\frac12$ each, both terminal, and a rule that breaks the tie at $x_2$ toward $a_2$ when the law at $x_1$ is $\delta_0$ and toward $a_1$ otherwise. That witness is context for the statement, not a second statement.

## Depends on

- [Distributional Bellman optimality operator](../distributional-control/distributional-bellman-optimality-operator.md)
- [Finite MDP with a joint reward and next-state kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md)

## Proof depends on

- [Distributional Bellman optimality operator](../distributional-control/distributional-bellman-optimality-operator.md)
- [Distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md)
- [The return distribution solves the distributional Bellman equation](../return-distributions-and-policy-evaluation/distributional-bellman-equation.md)
- [The return distribution has finite moments](../return-distributions-and-policy-evaluation/return-distribution-has-finite-moments.md)
- [Greedy policies for a return-distribution function](../distributional-control/greedy-policies-for-return-distributions.md)
- [Return distribution of a policy](../return-distributions-and-policy-evaluation/return-distribution-of-a-policy.md)

## Expansion

**Realization in the setting of these pages (derived here, not in the source).** Fix $\gamma \in (0,1)$, let $S_\gamma(t) = \gamma t$ and let $\nu_c = \frac12 \delta_{c-1} + \frac12 \delta_{c+1}$ for $c \in \mathbb{R}$. The MDP $M_0$ has states $x_1, x_2, x_3$, actions $a_1, a_2$ and a product reward–transition kernel:

- from $x_1$, both actions give reward $0$ and lead to $x_2$;
- from $x_2$, action $a_1$ gives reward $0$ and action $a_2$ gives reward $1$ or $-1$ with probability $\frac12$ each; both lead to $x_3$;
- from $x_3$, both actions give reward $0$ and lead back to $x_3$.

All rewards are bounded, so $M_q < \infty$ for every $q$. Define a greedy selection rule $\eta \mapsto \pi_\eta$ on $\mathscr{P}_1(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ by deterministic choices: at $x_1$ and at $x_3$ choose the action with the strictly larger mean if there is one and $a_1$ if the means tie; at $x_2$ choose the action with the strictly larger mean if there is one, and if $m(\eta)(x_2, a_1) = m(\eta)(x_2, a_2)$ choose $a_2$ when $\eta^{(x_1, a_1)} = \eta^{(x_1, a_2)} = \delta_0$ and $a_1$ otherwise. Let $\mathcal{T}$ be its optimality operator; it has no fixed point in $\mathscr{P}_1(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$, which proves the statement.

The rule picks a mean-maximizing action at every state for every input, so it is a greedy selection rule on $\mathscr{P}_1(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$. Suppose $Z = \mathcal{T}Z$ and let $c$ be the action chosen at $x_3$. Then $Z(x_3, a) = (S_\gamma)_\# Z(x_3, c)$ for both $a$, so the two components at $x_3$ are equal, to a law $L_3$ with $L_3 = (S_\gamma)_\# L_3$. Hence $L_3$ is the law of $\gamma^k U$ for every $k$, with $U \sim L_3$; letting $k \to \infty$ gives $L_3 = \delta_0$. Then $Z(x_2, a_1) = \delta_0$ and $Z(x_2, a_2) = \nu_0$, whose means tie at $0$. Both actions at $x_1$ give the same law $L_1 = (S_\gamma)_\# Z(x_2, a)$, with $a$ the action chosen at $x_2$. If $L_1 = \delta_0$ the rule chooses $a_2$ and $(\mathcal{T}Z)(x_1, \cdot) = (S_\gamma)_\# \nu_0 \ne \delta_0$ because $\gamma > 0$; otherwise it chooses $a_1$ and $(\mathcal{T}Z)(x_1, \cdot) = \delta_0 \ne L_1$. Both contradict $Z = \mathcal{T}Z$.

**Oscillation (derived here, not part of the statement).** Let $Z^0$ be the [return distribution](../return-distributions-and-policy-evaluation/return-distribution-of-a-policy.md) of the policy that plays $a_2$ at $x_2$ and $a_1$ elsewhere. Then for both actions $a$, $(\mathcal{T}^k Z^0)^{(x_1, a)} = \delta_0$ for odd $k$ and $(S_\gamma)_\# \nu_0$ for even $k$, while the components at $x_2$ and $x_3$ stay those of $Z^0$. Indeed, $Z^0$ solves its [distributional Bellman equation](../return-distributions-and-policy-evaluation/distributional-bellman-equation.md): $Z^0(x_3, \cdot) = \delta_0$, $Z^0(x_2, a_1) = \delta_0$, $Z^0(x_2, a_2) = \nu_0$, $Z^0(x_1, \cdot) = (S_\gamma)_\# \nu_0$. Along the iterates the two components at $x_1$ are equal and those at $x_3$ are $\delta_0$, so the choices there are $a_1$ by the tie rule and do not matter. Applying $\mathcal{T}$ leaves the components at $x_2$ and $x_3$ unchanged, the means at $x_2$ always tie, and the component at $x_1$ switches between $(S_\gamma)_\# \nu_0$ and $\delta_0$ at each step. The rule that breaks every tie at $x_2$ toward $a_2$ gives an optimality operator on $M_0$ with fixed point $Z^0$, so whether a fixed point exists depends on the tie-breaking rule.

**Relation to the source witness.** Bellemare, Dabney and Munos state the tie-breaking as "pick $a_2$ if $Z(x_1) = 0$", where $x_1$ has a single transition; with a common action set the condition is read on both actions at $x_1$. They model termination by terminal actions with no discount; with an absorbing state and $\gamma = 1$ the argument would fail, because $Z(x_3, \cdot)$ would no longer be forced to be $\delta_0$. Hence $\gamma \in (0,1)$; at $\gamma = 0$ the operator is constant and has a fixed point. The discounted absorbing-state version therefore needs the step that forces $Z(x_3, \cdot) = \delta_0$ at a fixed point, which the source does not give, and the source's proof exhibits an alternating orbit without a separate argument that no fixed point exists; the case analysis above supplies one for $M_0$. The source witness and this realization are related by that translation; the source states no equivalence between them.

## Sources

- M. G. Bellemare, W. Dabney and R. Munos, *A Distributional Perspective on Reinforcement Learning*, Proceedings of the 34th International Conference on Machine Learning (ICML 2017); numbers from arXiv:1707.06887v1, <https://arxiv.org/abs/1707.06887v1>: Section 3.4, Proposition 2 of the main text and the paragraph after it.
