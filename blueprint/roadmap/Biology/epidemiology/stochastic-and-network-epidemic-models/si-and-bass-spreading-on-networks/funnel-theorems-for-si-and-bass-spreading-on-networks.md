# Funnel theorems for the SI and Bass models on networks

**Model.** Individuals $\mathcal{M} = \{1, \dots, M\}$ have states $X_j(t) \in \{0, 1\}$ (1 = infected/adopter). Initial states are independent with $\mathbb{P}(X_j(0) = 1) = I^0_j \in [0, 1]$. A susceptible $j$ becomes infected at rate

$$\lambda_j(t) = p_j + \sum_{k \in \mathcal{M}} q_{k,j} X_k(t),$$

with external rate $p_j \ge 0$ and peer rates $q_{k,j} \ge 0$ (an edge $k \to j$ when $q_{k,j} > 0$); infection is permanent. The SI epidemic model is the case $p_j \equiv 0$, the Bass innovation-diffusion model the case $I^0_j \equiv 0$. For $\Omega \subset \mathcal{M}$ let $S_\Omega = \mathbb{P}(X_k(t) = 0 \ \forall k \in \Omega)$. A node $m$ is *influential to* $\Omega$ if $m \in \Omega$ or there is a directed path from $m$ to $\Omega$.

**Theorem (non-negative correlation of non-infection).** For pairwise disjoint $\Omega_1, \dots, \Omega_L \subset \mathcal{M}$,

$$S_{\cup_l \Omega_l} \ge \prod_{l=1}^L S_{\Omega_l}, \qquad t \ge 0.$$

The inequality is strict for all $t > 0$ if some node is influential to two different sets $\Omega_l$, $\Omega_{\tilde l}$, and it is an equality for all $t \ge 0$ otherwise.

**Funnel theorem.** Fix $j$ and a partition $\{A_1, \dots, A_L, \{j\}\}$ of $\mathcal{M}$. Let $\mathcal{N}^{A, p_j}$ be the network with all internal influences on $j$ that do not come from $A$ removed ($q_{k,j} := 0$ for $k \notin A$), and $\mathcal{N}^{p_j}$ the network with all internal influences on $j$ removed, so that $[S^{p_j}_j] = (1 - I^0_j)e^{-p_j t}$. Then

$$S_j \ge \frac{\prod_{l=1}^L S^{A_l, p_j}_j}{\big(S^{p_j}_j\big)^{L-1}}, \qquad t \ge 0 \qquad \text{(funnel inequality)}.$$

Call $j$ a *funnel node* of $\{A_l\}$ if no node other than $j$ is influential to $j$ both in $\mathcal{N}^{A_l}$ and in $\mathcal{N}^{A_{\tilde l}}$ for some $l \ne \tilde l$; every vertex cut separating the $A_l$ is a funnel node. If $j$ is a funnel node the funnel inequality is an equality for all $t \ge 0$; otherwise it is strict for all $t > 0$.

## Expansion

Non-infection events are decreasing functions of the independent infection clocks, so they are positively associated, giving the product lower bound; equality holds exactly when no single node can transmit to two of the sets, since then the events depend on disjoint sets of clocks. The funnel theorem conditions on $j$ staying susceptible: until $j$ is infected, infection cannot pass through $j$, so if $j$ funnels all paths between the parts $A_l$, the parts evolve independently and the non-infection probability of $j$ factorizes into the per-part survival factors, each counted with one external factor $e^{-p_j t}$ too many. These identities give explicit solutions of the master equations on lines, circles and trees, and the gap terms quantify the effect of cycles.

## Sources

- Gadi Fibich, Tomer Levin and Steven Schochet, "Funnel theorems for spreading on networks", Chaos: An Interdisciplinary Journal of Nonlinear Science 35 (2025), 073109, <https://doi.org/10.1063/5.0269855>; numbering as in arXiv:2411.12037: Definition 2.2 (influential node), Theorem 3.1, Theorem 4.1, Lemma 4.1 and Theorem 4.2.
