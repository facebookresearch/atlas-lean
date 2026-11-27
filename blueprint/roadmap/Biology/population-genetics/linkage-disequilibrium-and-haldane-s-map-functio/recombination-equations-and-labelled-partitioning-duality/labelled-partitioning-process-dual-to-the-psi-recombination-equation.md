# Labelled partitioning process dual to the $\psi$-recombination equation

**Setting.** Haploid types are sequences $x = (x_1,\dots,x_n) \in X = X_1 \times \cdots \times X_n$ over sites $S = \{1,\dots,n\}$ (each $X_i$ locally compact Hausdorff), and the type distribution of an infinite population is $\omega_t \in \mathcal{P}(X)$. For $A \subseteq S$ let $\nu_A$ be the marginal of $\nu$ on $X_A = \prod_{i\in A} X_i$. For a partition $\mathcal{A}$ of $S$ the **recombinator** is $\mathcal{R}_{\mathcal{A}}(\nu) = \bigotimes_{A \in \mathcal{A}} \nu_A$, and with rates $\varrho_{\mathcal{A}} \ge 0$ the **$\psi$-recombination equation** is

$$\dot\omega_t = \psi(\omega_t) + \sum_{\mathcal{A}} \varrho_{\mathcal{A}}\bigl(\mathcal{R}_{\mathcal{A}}(\omega_t) - \omega_t\bigr),$$

where $\psi$ is a total-variation Lipschitz vector field on $\mathcal{P}(X)$ (selection, mutation, ...) acting through a single **active site** $i_\bullet$:

- (a) if $\nu = \nu_C \otimes \nu_D$ with $\{C,D\}$ a partition of $S$ and $i_\bullet \in C$, then $\psi(\nu) = \psi(\nu)_C \otimes \nu_D$;
- (b) $\psi$ is affine on each set of measures sharing the same marginal at $i_\bullet$.

The block of $\mathcal{A}$ containing $i_\bullet$ is its **head** $A_\bullet$; the other blocks form the **tail** $\mathcal{A}^\circ$.

**Input duality.** Suppose $\dot\omega^{(0)}_t = \psi(\omega^{(0)}_t)$ is dual to a Feller process $Y$ on a Polish space $E$ with generator $\mathcal{Q}$ and duality function $h : \mathcal{P}(X)\times E \to \mathcal{P}(X)$, i.e. $h(\Psi^{(0)}_t\nu, y) = \mathbb{E}[h(\nu, Y_t)\mid Y_0=y]$, where for every $y$ the map $h(\cdot,y)$ satisfies (a)–(b), there is an "empty genealogy" $\varnothing_E \in E$ with $h(\nu,\varnothing_E) = \nu$, and the usual smoothness/domain conditions hold. (Examples: $Y_t = Y_0 + t$ with $h(\nu,y)=\Psi^{(0)}_y(\nu)$; the Yule line-counting process of the deterministic ancestral selection graph for selection; per-site first-mutation chains for mutation.)

**Labelled partitioning process.** Its states are pairs $(\mathcal{A}, v)$ with $\mathcal{A}$ a partition of $S$ and labels $v = (v_A)_{A\in\mathcal{A}} \in E^{\mathcal{A}}$. Independently for every block $A$ and every partition $\mathcal{B}$, at rate $\varrho_{\mathcal{B}}$ the block $A$ is replaced by the nonempty pieces $A \cap B$, $B \in \mathcal{B}$; the piece $A \cap B_\bullet$ keeps the label $v_A$ and every piece $A \cap B$ with $B \in \mathcal{B}^\circ$ gets the label $\varnothing_E$ (if $A \subseteq B \in \mathcal{B}^\circ$ this just resets $v_A$). Between these events the labels evolve as independent copies of $Y$.

**Theorem.** Under these assumptions the labelled partitioning process $\Sigma_t = (\mathcal{A}_t, V_t)$ is dual to the $\psi$-recombination equation with duality function $H(\mathcal{A}, v; \nu) = \bigotimes_{A\in\mathcal{A}} h(\nu, v_A)_A$. In particular

$$\omega_t = \mathbb{E}\Bigl[\,\bigotimes_{A \in \mathcal{A}_t} h(\omega_0, V_{A,t})_A \;\Big|\; \mathcal{A}_0 = \{S\},\ V_{S,0} = \varnothing_E\Bigr].$$

The label of the head block is never split off or reset, so it is simply a copy of $Y$.

## Expansion

Backward in time, a block of the genome hit by a $\mathcal{B}$-recombination event has its pieces inherited from independent parents; by the head-only action of $\psi$ (property (a) for $h$), only the piece in the head of $\mathcal{B}$ carries the past genealogy of $\psi$-events, while the other pieces start fresh genealogies. Formally, one expands $\Psi_\delta(\nu)$ to first order in $\delta$, uses (b) and (a) for $h(\cdot,y)$ to obtain

$$\mathcal{G}h(y,\cdot)(\nu) = \mathcal{Q}h(\cdot,\nu)(y) + \sum_{\mathcal{B}}\varrho_{\mathcal{B}}\Bigl(h(y,\nu)_{B_\bullet}\otimes\bigotimes_{B\in\mathcal{B}^\circ}h(\varnothing_E,\nu)_B - h(y,\nu)\Bigr),$$

and then the product rule over the blocks of $H$ shows that the forward generator applied to $H$ equals the labelled-partition generator applied to $H$; the Feller generator criterion for duality concludes. Without $\psi$ the labels are irrelevant and the result reduces to the classical partitioning-process solution of the pure recombination equation.

## Sources

- Frederic Alberti, "Labeled partitions in action: Recombination, selection, mutation and more", *Stochastics and Dynamics* 24 (2024), 2450014, <https://doi.org/10.1142/s021949372450014x>. Numbering as in the preprint arXiv:2203.10874v2, <https://arxiv.org/abs/2203.10874v2>: Section 2 (Eq. for the $\psi$-recombination equation, Assumption 1, Definition 2.2), Section 3 (Assumption 2, Definition 3.6, Lemma 3.7, Theorem 3.8, Remark 3.5).
