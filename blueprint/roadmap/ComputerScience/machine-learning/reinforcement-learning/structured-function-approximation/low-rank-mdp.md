# Low-rank MDP

A low-rank MDP has transition operators that admit a factorization $T_h(x' \mid x,a) = \langle \phi^\star_h(x,a), \mu^\star_h(x') \rangle$ of dimension $d$, with both embeddings unknown. The dimension need not be the minimal rank, and the factorization need not be unique.

**Setting.** An episodic MDP with horizon $H$, state space $\mathcal{X}$ of arbitrary size, finite action set $\mathcal{A} = \{1, \dots, K\}$, a fixed starting state $x_0$ with a single available action at time $0$, and non-stationary transition operators $T_h : \mathcal{X}\times\mathcal{A} \to \Delta(\mathcal{X})$ for $h \in \{0, \dots, H-1\}$. Policies map states to distributions over actions.

**Definition.** An operator $T : \mathcal{X}\times\mathcal{A} \to \Delta(\mathcal{X})$ *admits a low-rank decomposition with dimension $d$* if there are embeddings $\phi^\star : \mathcal{X}\times\mathcal{A} \to \mathbb{R}^d$ and $\mu^\star : \mathcal{X} \to \mathbb{R}^d$ with

$$
T(x' \mid x, a) = \langle \phi^\star(x,a), \mu^\star(x') \rangle \qquad \text{for all } x, x' \in \mathcal{X},\ a \in \mathcal{A},
$$

normalized by $\lVert\phi^\star(x,a)\rVert_2 \le 1$ for all $(x,a)$ and $\big\lVert \int \mu^\star(x) g(x)\, dx \big\rVert_2 \le \sqrt d$ for every $g : \mathcal{X} \to [0,1]$. The MDP is a *low-rank MDP* of dimension $d$ if each $T_h$ admits such a decomposition, with embeddings $\phi^\star_h, \mu^\star_h$.

**Realizability (Assumption 1).** The learner is given finite classes $\Phi \subset \{\mathcal{X}\times\mathcal{A} \to \mathbb{R}^d\}$ and $\Upsilon \subset \{\mathcal{X} \to \mathbb{R}^d\}$ with $\phi^\star_h \in \Phi$ and $\mu^\star_h \in \Upsilon$ for every $h$. The source shows that the low-rank assumption without such classes does not allow guarantees independent of the number of states.

**Relation to linear MDPs.** Representation learning here means learning, from given candidate classes $\Phi$ and $\Upsilon$ that contain the true embeddings, features that predict the transition law; it need not identify $\phi^\star$ itself. The source notes that the same transition structure has been called a linear MDP, and that linear-MDP algorithms assume the feature maps $\phi^\star_h$ known (see [linear MDP](linear-mdp.md)); here the embeddings are unknown. No linear reward structure is assumed: the source works in a reward-free formulation and plans afterwards for an explicitly given reward. By Lemma 1 of the source, an accurate learned model $(\hat\phi_h, \hat\mu_h)$ makes Bellman backups of every bounded value function approximately linear in $\hat\phi_h$ on the state-action distributions of all policies. That is the sense in which a learned representation supports linear methods downstream.

## Depends on

- [Probability measure](../../../../Probability/foundations/probability-measures/is-probability-measure.md)

## Proof depends on

None.

## Expansion

The source attributes the integrated normalization on $\mu^\star$ to the proof of the weight bound for linear MDPs. It also compares low-rank MDPs with other structural models. A low-rank MDP of dimension $d$ can require $M$ latent states for any block-MDP representation on $M$ states (Proposition 1). Rank $O(n^2)$ is compatible with latent-variable (nonnegative) dimension $2^{\Omega(n)}$ (Proposition 2). For any candidate model class the [witness rank](witness-rank.md) is at most $d$ with norm parameter $O(\sqrt d)$ (Proposition 7). The algorithms that exploit such ranks enumerate function classes and are not computationally tractable, which motivates oracle-based methods.

## Sources

- A. Agarwal, S. Kakade, A. Krishnamurthy and W. Sun, "FLAMBE: Structural Complexity and Representation Learning of Low Rank MDPs", Advances in Neural Information Processing Systems 33 (NeurIPS 2020). Numbers from arXiv:2006.10814v2: Section 2 (setting), Definition 1, Assumption 1, Eq. (1), Lemma 1, Definition 2, Propositions 1, 2 and 7, Section 3 (related work), Appendix A. <https://arxiv.org/abs/2006.10814v2>
