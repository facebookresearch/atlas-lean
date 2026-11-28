# A distributional optimality operator without a fixed point

In the undiscounted model with terminal actions, not every distributional Bellman optimality operator has a fixed point.

This page uses the undiscounted model with terminal actions of Bellemare, Dabney and Munos. It lies outside the discounted setting ($\gamma < 1$, no terminal actions) of the other pages of this topic, so the definitions it needs are stated here.

A *finite MDP with terminal actions* has finite nonempty sets $\mathcal{X}$ of states and $\mathcal{A}$ of actions and, for each $(x,a)$, a [probability measure](../../../../../Probability/foundations/probability-measures/is-probability-measure.md) $\mathsf{q}(\cdot \mid x,a)$ on $\mathbb{R} \times (\mathcal{X} \cup \{\dagger\})$: a reward and either a next state or the outcome $\dagger$, which ends the episode. The pair $(x,a)$ is *terminal* when $\mathsf{q}(\mathbb{R} \times \{\dagger\} \mid x,a) = 1$. Rewards are *bounded* when every $\mathsf{q}(\cdot \mid x,a)$ is concentrated on $[-K, K] \times (\mathcal{X} \cup \{\dagger\})$ for one $K$. For a [stochastic policy](../../stochastic-policies-and-discounted-occupancy/stochastic-policy.md) $\pi$ and a [return-distribution function](../return-distributions-and-policy-evaluation/return-distribution-function.md) $\eta$, the undiscounted distributional Bellman operator is

$$(\mathcal{T}^\pi_{1} \eta)^{(x,a)}(B) = \mathsf{q}(B \times \{\dagger\} \mid x,a) + \sum_{(x',a') \in \mathcal{X} \times \mathcal{A}} \pi(a' \mid x') \int_{\mathbb{R}} (f_{r})_\# \eta^{(x',a')}(B) \, \mathsf{q}(dr \times \{x'\} \mid x,a)$$

for Borel sets $B \subseteq \mathbb{R}$, where $f_r(t) = r + t$ and $(f_r)_\#$ is the [law](../../../../../Probability/foundations/probability-measures/probability-measure-map.md) of the shifted variable. It is the law of $R + G'$, with $(R, X') \sim \mathsf{q}(\cdot \mid x,a)$ and $G' = 0$ if $X' = \dagger$; otherwise $A' \sim \pi(\cdot \mid X')$ and $G'$ is drawn freshly from $\eta^{(X',A')}$ conditionally on $(R, X', A')$. With bounded rewards it maps $\mathscr{P}_1(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ into itself. A *greedy selection rule* assigns to each $\eta \in \mathscr{P}_1(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ a [greedy policy](../distributional-control/greedy-policies-for-return-distributions.md) $\pi_\eta$ for $\eta$, and its *distributional Bellman optimality operator* is $\mathcal{T} \eta = \mathcal{T}^{\pi_\eta}_{1} \eta$.

**Statement.** There exist a finite MDP with terminal actions and bounded rewards and a greedy selection rule whose undiscounted distributional Bellman optimality operator $\mathcal{T}$ has no fixed point $Z = \mathcal{T} Z$ in $\mathscr{P}_1(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$.

Bellemare, Dabney and Munos's witness has states $x_1, x_2$ and actions $a_1, a_2$. From $x_1$ both actions give reward $0$ and lead to $x_2$ (their single transition from $x_1$). At $x_2$, action $a_1$ gives reward $0$ and action $a_2$ gives reward $1$ or $-1$ with probability $\frac12$ each, and both actions are terminal. The rule chooses a mean-maximizing action at each state, $a_1$ on ties, except that on a tie at $x_2$ it chooses $a_2$ when $Z^{(x_1, a_1)} = Z^{(x_1, a_2)} = \delta_0$.

## Depends on

- [Probability measure](../../../../../Probability/foundations/probability-measures/is-probability-measure.md)
- [Law of a random element](../../../../../Probability/foundations/probability-measures/probability-measure-map.md)
- [Stochastic policy](../../stochastic-policies-and-discounted-occupancy/stochastic-policy.md)
- [Return-distribution function](../return-distributions-and-policy-evaluation/return-distribution-function.md)
- [Greedy policies for a return-distribution function](../distributional-control/greedy-policies-for-return-distributions.md)

## Proof depends on

- [Greedy policies for a return-distribution function](../distributional-control/greedy-policies-for-return-distributions.md)

## Expansion

**Proof in the source's model.** The rule is greedy: it picks a strict mean-maximizer when there is one and breaks ties only among maximizers. Let $\nu_0 = \frac12 \delta_{-1} + \frac12 \delta_1$. Suppose $Z = \mathcal{T} Z$. Both pairs at $x_2$ are terminal, so $Z^{(x_2, a_1)} = \delta_0$ and $Z^{(x_2, a_2)} = \nu_0$ whatever $Z$ is, and their means tie at $0$. Both actions at $x_1$ lead to $x_2$ with reward $0$, so $Z^{(x_1, a)} = Z^{(x_2, c)}$ for both $a$, where $c$ is the action the rule chooses at $x_2$. If $Z^{(x_1, a_1)} = Z^{(x_1, a_2)} = \delta_0$, then $c = a_2$ and $Z^{(x_1, a)} = \nu_0 \ne \delta_0$. Otherwise $c = a_1$ and $Z^{(x_1, a)} = \delta_0$ for both $a$, which is the excluded case. Both cases contradict $Z = \mathcal{T} Z$. Bellemare, Dabney and Munos argue by showing that the iterates $\mathcal{T}^k Z^*$ alternate at $x_1$ between $Z^*(x_2, a_1)$ and $Z^*(x_2, a_2)$; this case analysis, which shows directly that no fixed point exists, is derived here. Their rule tests "$Z(x_1) = 0$" at a state with a single transition; with a common action set the test is read on both actions at $x_1$.

**A discounted analogue in the setting of the other pages (derived here, not in the source, and not part of the statement).** The same phenomenon occurs with $\gamma < 1$ when termination is replaced by an absorbing zero-reward state. Fix $\gamma \in (0,1)$, let $S_\gamma(t) = \gamma t$ and let $\nu_c = \frac12 \delta_{c-1} + \frac12 \delta_{c+1}$ for $c \in \mathbb{R}$. The MDP $M_0$ has states $x_1, x_2, x_3$, actions $a_1, a_2$ and a product reward–transition kernel:

- from $x_1$, both actions give reward $0$ and lead to $x_2$;
- from $x_2$, action $a_1$ gives reward $0$ and action $a_2$ gives reward $1$ or $-1$ with probability $\frac12$ each; both lead to $x_3$;
- from $x_3$, both actions give reward $0$ and lead back to $x_3$.

All rewards are bounded, so $M_q < \infty$ for every $q$. Define a greedy selection rule $\eta \mapsto \pi_\eta$ on $\mathscr{P}_1(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ by deterministic choices: at $x_1$ and at $x_3$ choose the action with the strictly larger mean if there is one and $a_1$ if the means tie; at $x_2$ choose the action with the strictly larger mean if there is one, and if $m(\eta)(x_2, a_1) = m(\eta)(x_2, a_2)$ choose $a_2$ when $\eta^{(x_1, a_1)} = \eta^{(x_1, a_2)} = \delta_0$ and $a_1$ otherwise. Let $\mathcal{T}$ be its [distributional Bellman optimality operator](../distributional-control/distributional-bellman-optimality-operator.md); it has no fixed point in $\mathscr{P}_1(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$.

The rule picks a mean-maximizing action at every state for every input, so it is a greedy selection rule on $\mathscr{P}_1(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$. Suppose $Z = \mathcal{T}Z$ and let $c$ be the action chosen at $x_3$. Then $Z(x_3, a) = (S_\gamma)_\# Z(x_3, c)$ for both $a$, so the two components at $x_3$ are equal, to a law $L_3$ with $L_3 = (S_\gamma)_\# L_3$. Hence $L_3$ is the law of $\gamma^k U$ for every $k$, with $U \sim L_3$; letting $k \to \infty$ gives $L_3 = \delta_0$. Then $Z(x_2, a_1) = \delta_0$ and $Z(x_2, a_2) = \nu_0$, whose means tie at $0$. Both actions at $x_1$ give the same law $L_1 = (S_\gamma)_\# Z(x_2, a)$, with $a$ the action chosen at $x_2$. If $L_1 = \delta_0$ the rule chooses $a_2$ and $(\mathcal{T}Z)(x_1, \cdot) = (S_\gamma)_\# \nu_0 \ne \delta_0$ because $\gamma > 0$; otherwise it chooses $a_1$ and $(\mathcal{T}Z)(x_1, \cdot) = \delta_0 \ne L_1$. Both contradict $Z = \mathcal{T}Z$.

**Oscillation (derived here, not part of the statement).** Let $Z^0$ be the [return distribution](../return-distributions-and-policy-evaluation/return-distribution-of-a-policy.md) of the policy that plays $a_2$ at $x_2$ and $a_1$ elsewhere. Then for both actions $a$, $(\mathcal{T}^k Z^0)^{(x_1, a)} = \delta_0$ for odd $k$ and $(S_\gamma)_\# \nu_0$ for even $k$, while the components at $x_2$ and $x_3$ stay those of $Z^0$. Indeed, $Z^0$ solves its [distributional Bellman equation](../return-distributions-and-policy-evaluation/distributional-bellman-equation.md): $Z^0(x_3, \cdot) = \delta_0$, $Z^0(x_2, a_1) = \delta_0$, $Z^0(x_2, a_2) = \nu_0$, $Z^0(x_1, \cdot) = (S_\gamma)_\# \nu_0$. Along the iterates the two components at $x_1$ are equal and those at $x_3$ are $\delta_0$, so the choices there are $a_1$ by the tie rule and do not matter. Applying $\mathcal{T}$ leaves the components at $x_2$ and $x_3$ unchanged, the means at $x_2$ always tie, and the component at $x_1$ switches between $(S_\gamma)_\# \nu_0$ and $\delta_0$ at each step. The rule that breaks every tie at $x_2$ toward $a_2$ gives an optimality operator on $M_0$ with fixed point $Z^0$, so whether a fixed point exists depends on the tie-breaking rule.

**Relation between the two.** The discounted analogue needs the step that forces $Z(x_3, \cdot) = \delta_0$ at a fixed point, and that step uses $\gamma < 1$. With an absorbing state and $\gamma = 1$, the component at $x_3$ is unconstrained and the argument fails; at $\gamma = 0$ the operator is constant and has a fixed point. The source states neither a discounted version nor an equivalence between the two models.

## Sources

- M. G. Bellemare, W. Dabney and R. Munos, *A Distributional Perspective on Reinforcement Learning*, Proceedings of the 34th International Conference on Machine Learning (ICML 2017); numbers from arXiv:1707.06887v1, <https://arxiv.org/abs/1707.06887v1>: Section 3.4, Proposition 2 of the main text and the paragraph after it, with the example of Proposition 1 and Figure 2 ("Undiscounted two-state MDP"; "Both actions are terminal").
