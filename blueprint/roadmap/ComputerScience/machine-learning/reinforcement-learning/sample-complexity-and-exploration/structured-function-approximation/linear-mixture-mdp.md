# Linear mixture MDP

A linear mixture MDP has transition probabilities that are linear in an unknown parameter: $P_h(s' \mid s,a) = \langle \phi(s' \mid s,a), \theta_h \rangle$ for a known feature map of state, action and next state. It is a model-based assumption, different from a linear MDP, whose features depend on $(s,a)$ only.

**Setting.** An episodic MDP $M(\mathcal{S}, \mathcal{A}, H, \{r_h\}, \{P_h\})$ has a countable state space $\mathcal{S}$, a finite action set $\mathcal{A}$, horizon $H$, deterministic known rewards $r_h : \mathcal{S} \times \mathcal{A} \to [0,1]$ and stage-dependent transition probabilities $P_h(s' \mid s,a)$.

**Features.** A feature map $\phi(\cdot \mid \cdot, \cdot) : \mathcal{S} \times \mathcal{A} \times \mathcal{S} \to \mathbb{R}^d$ is admissible if for every function $V : \mathcal{S} \to [0,1]$ and every $(s,a)$

$$
\lVert \phi_V(s,a) \rVert_2 \le 1, \qquad \text{where } \phi_V(s,a) = \sum_{s' \in \mathcal{S}} \phi(s' \mid s, a) V(s') .
$$

**Definition.** For $B > 0$, $M$ is an *inhomogeneous episodic $B$-bounded linear mixture MDP* if there are an admissible $\phi$ and vectors $\theta_h \in \mathbb{R}^d$ with $\lVert \theta_h \rVert_2 \le B$ such that

$$
P_h(s' \mid s,a) = \langle \phi(s' \mid s,a), \theta_h \rangle \qquad \text{for all } (s,a,s') \text{ and } h \in [H].
$$

The feature map is known; the parameters $\Theta^\star = (\theta^\star_h)_{h \in [H]}$ are unknown. In the *discounted* version (discount $\gamma \in [0,1)$) a single $\theta$ with $\lVert\theta\rVert_2 \le B$ gives $P(s' \mid s,a) = \langle \phi(s'\mid s,a), \theta \rangle$.

**Consequences used by algorithms.** For every $V : \mathcal{S} \to [0,1]$, and by linearity every bounded $V$, $(P_h V)(s,a) = \sum_{s'} P_h(s' \mid s,a)V(s') = \langle \phi_V(s,a), \theta_h \rangle$, so one-step expectations of bounded value functions are linear in the known vector $\phi_V(s,a)$; regressing observed $V(s_{h+1})$ on $\phi_V(s_h,a_h)$ ("value-targeted regression") estimates $\theta_h$. The same identity with $V^2$ makes the second moment $[P_hV^2]$ linear as well. The conditional variance $[P_hV^2] - [P_hV]^2$ is not linear in $\theta_h$; algorithms estimate the two moments separately and combine the estimates.

**Contrast with linear MDPs.** In a [linear MDP](linear-mdp.md), $P_h(\cdot \mid s,a) = \langle \phi(s,a), \mu_h(\cdot) \rangle$ with known $(s,a)$-features and unknown, possibly infinite-dimensional measures; here the unknown is a $d$-dimensional vector and the features also depend on the next state.

## Depends on

- [Expectation under a probability mass function](../../../../../Probability/distributions/discrete/expectation-under-a-probability-mass-function/expect.md)

## Proof depends on

None.

## Expansion

The source also calls these linear kernel MDPs: each $P_h$ is a linear combination, with weights $\theta_{h,i}$, of the $d$ known basis functions $\phi_i(\cdot \mid s,a)$. Its algorithms use the identity $(P_hV)(s,a) = \langle \phi_V(s,a), \theta_h \rangle$ for the first moment and the same identity with $V^2$ for the second moment (its Eq. (5.4)). The source credits the definition to Jia et al. (2020) and Ayoub et al. (2020).

## Sources

- D. Zhou, Q. Gu and Cs. Szepesvári, "Nearly Minimax Optimal Reinforcement Learning for Linear Mixture Markov Decision Processes", Conference on Learning Theory (COLT 2021), PMLR 134:4532–4576. Numbers from arXiv:2012.08507v2: Section 3 (episodic and discounted MDPs), Eq. (3.3), Definitions 3.1 and 3.2, Eq. (5.4). <https://arxiv.org/abs/2012.08507v2>
