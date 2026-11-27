# Linear MDP

A linear MDP is an episodic Markov decision process whose stage-$h$ transition kernel and reward are both linear in a known feature map $\phi(x,a) \in \mathbb{R}^d$, with unknown stage-dependent signed measures $\mu_h$ and vectors $\theta_h$. It is a structural assumption on the dynamics, stronger than linear realizability of $Q^\star$.

**Setting.** An episodic MDP $(\mathcal{S}, \mathcal{A}, H, \mathbb{P}, r)$ has a measurable state space $\mathcal{S}$ (possibly infinite), a finite action set $\mathcal{A}$, horizon $H \in \mathbb{Z}_{>0}$, transition kernels $\mathbb{P}_h(\cdot \mid x, a)$ and deterministic rewards $r_h : \mathcal{S} \times \mathcal{A} \to [0,1]$ for $h \in [H]$. Transitions and rewards may differ from stage to stage.

**Definition.** The MDP is a *linear MDP with feature map* $\phi : \mathcal{S} \times \mathcal{A} \to \mathbb{R}^d$ if for every $h \in [H]$ there are $d$ signed measures $\mu_h = (\mu_h^{(1)}, \dots, \mu_h^{(d)})$ on $\mathcal{S}$ and a vector $\theta_h \in \mathbb{R}^d$ such that for all $(x,a)$

$$
\mathbb{P}_h(\cdot \mid x, a) = \langle \phi(x,a), \mu_h(\cdot) \rangle, \qquad r_h(x,a) = \langle \phi(x,a), \theta_h \rangle .
$$

The feature map $\phi$ is known to the learner; $\mu_h$ and $\theta_h$ are unknown. The normalization is $\lVert \phi(x,a) \rVert_2 \le 1$ for all $(x,a)$ and $\max\{\lVert \mu_h(\mathcal{S}) \rVert_2, \lVert \theta_h \rVert_2\} \le \sqrt{d}$ for all $h$, where $\mu_h(\mathcal{S}) \in \mathbb{R}^d$ is the vector of total masses.

**Integrated normalization.** Some results about linear MDPs are stated under the additional condition

$$
\Big\lVert \int_{\mathcal{S}} g(x')\, d\mu_h(x') \Big\rVert_2 \le \sqrt d \qquad \text{for every measurable } g : \mathcal{S} \to [0,1] \text{ and every } h,
$$

which is how Agarwal, Kakade, Krishnamurthy and Sun normalize the second embedding of a low-rank MDP; their footnote points to the proof of Jin et al.'s Lemma B.1 for this form. It is a separate condition: for signed measures $\mu_h$, the bound on the vector of total masses $\mu_h(\mathcal{S})$ does not imply it.

**Remarks recorded in the source.**

- Since each $\mathbb{P}_h(\cdot \mid x,a)$ is a probability measure, $\phi(x,a)^{\mathsf T} \mu_h(\mathcal{S}) = 1$ and $\phi(x,a)^{\mathsf T} \mu_h(B) \ge 0$ for every measurable $B$; in particular the image of $\phi$ lies in an affine hyperplane.
- Tabular MDPs are the case $d = |\mathcal{S}||\mathcal{A}|$ with $\phi(x,a) = e_{(x,a)}$. Features in the probability simplex, with arbitrary probability measures $e_i^{\mathsf T} \mu_h$ and $\lVert \theta_h \rVert_\infty \le 1$, also give linear MDPs (rewards in $[0,1]$ need $\theta_h \in [0,1]^d$).
- The measures $\mu_h$ are unknown and may have infinitely many degrees of freedom, so a linear MDP is not a finite-parameter model of the dynamics.

**Scope.** The assumption constrains the transition model itself. Linear realizability of the optimal action-value function alone (some $\theta$ with $Q^\star_h = \langle \phi, \theta \rangle$) does not imply it; later work gives exponential lower bounds in that realizability-only setting, for example the [planning lower bound under linear realizability of the optimal action values](planning-lower-bound-under-q-star-realizability.md).

## Depends on

None.

## Proof depends on

None.

## Expansion

The definition is Assumption A of the source. The hyperplane constraint follows from $\phi(x,a)^{\mathsf T} \mu_h(\mathcal{S}) = \mathbb{P}_h(\mathcal{S} \mid x,a) = 1$. Bounds on value-function weights use an estimate of $\lVert \int V\, d\mu_h \rVert_2$ for bounded $V$, which the integrated normalization provides ($\le H\sqrt d$ for $0 \le V \le H$) and the total-mass bound does not.

## Sources

- C. Jin, Z. Yang, Z. Wang and M. I. Jordan, "Provably Efficient Reinforcement Learning with Linear Function Approximation", Conference on Learning Theory (COLT 2020), PMLR 125; journal version Mathematics of Operations Research 48(3):1496–1521, 2023, doi:10.1287/moor.2022.1309. Numbers from arXiv:1907.05388v2: Section 2 (setting), Assumption A, Examples 2.1–2.2, Proposition A.1. <https://arxiv.org/abs/1907.05388v2>
- A. Agarwal, S. Kakade, A. Krishnamurthy and W. Sun, "FLAMBE: Structural Complexity and Representation Learning of Low Rank MDPs", Advances in Neural Information Processing Systems 33 (NeurIPS 2020). Numbers from arXiv:2006.10814v2: Definition 1 and its footnote on the normalization ("See the proof of Lemma B.1 in Jin et al. (2019) for this form of the normalization assumption"). <https://arxiv.org/abs/2006.10814v2>
