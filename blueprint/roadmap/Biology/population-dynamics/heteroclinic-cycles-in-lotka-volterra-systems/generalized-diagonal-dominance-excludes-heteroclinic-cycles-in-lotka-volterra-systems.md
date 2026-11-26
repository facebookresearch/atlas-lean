# Generalized diagonal dominance excludes heteroclinic cycles in Lotka–Volterra systems

**Model.** For $N$ interacting species,
$$ \dot u_i = u_i\Big(b_i + \sum_{j=1}^N a_{ij}u_j\Big), \qquad i = 1,\dots,N, \qquad \mathbf{u} \in \mathbb{R}^N_{\ge 0}, $$
with intrinsic growth vector $\mathbf{b} \in \mathbb{R}^N$ and interaction matrix $A$ with negative self-interactions $a_{ii} < 0$. At a nonnegative equilibrium $\mathbf{x}$ the invasion rate of species $i$ is $r_i(\mathbf{x}) = b_i + (A\mathbf{x})_i$.

**Three graphs on equilibria.** For distinct nonnegative equilibria $\mathbf{x}, \mathbf{y}$ with supports $I, J$:
- *invasion graph*: $\mathbf{x} \to \mathbf{y}$ iff $r_j(\mathbf{x}) > 0$ for all $j \in J\setminus I$ and $r_i(\mathbf{y}) < 0$ for all $i \in I\setminus J$;
- *weak graph*: the same with $\ge 0$ and $\le 0$;
- *connection graph*: $\mathbf{x} \to \mathbf{y}$ iff some bounded complete orbit converges to $\mathbf{x}$ as $t \to -\infty$ and to $\mathbf{y}$ as $t \to +\infty$.

**Generalized strict diagonal dominance.** Let $B_{ij} = |a_{ij}|/|a_{ii}|$ for $i \ne j$, $B_{ii} = 0$, and let $\mathcal{H}_- = \{A : a_{ii} < 0 \text{ for all } i,\ \rho(B) < 1\}$. Equivalently there are weights $\mathbf{v} > 0$ with $|a_{ii}|v_i > \sum_{j\ne i}|a_{ij}|v_j$ for every $i$: weighted self-limitation outweighs all interspecific interactions.

**Theorem.** Let $A \in \mathcal{H}_-$. For every $\mathbf{b} \in \mathbb{R}^N$:
1. $A$ is Volterra–Lyapunov stable, and the semiflow has a global attractor;
2. the invasion, connection and weak graphs are all acyclic, and there is no nonconstant homoclinic orbit;
3. the semiflow is gradient with respect to its equilibria: some continuous $\mathcal{L}$ strictly decreases along every nonequilibrium trajectory, and the $\alpha$-limit of each bounded complete orbit is a single equilibrium.

No hyperbolicity is assumed. Concretely, if $\mathbf{w} > 0$ satisfies $M^{\mathsf T}\mathbf{w} > 0$ for the comparison matrix $M$ ($M_{ii} = |a_{ii}|$, $M_{ij} = -|a_{ij}|$), then $V_{\mathbf{w}}(\mathbf{x}) = \mathbf{w}^{\mathsf T}r(\mathbf{x})$ satisfies
$$ V_{\mathbf{w}}(\mathbf{y}) - V_{\mathbf{w}}(\mathbf{x}) \le -(M^{\mathsf T}\mathbf{w})^{\mathsf T}|\mathbf{y} - \mathbf{x}| < 0 $$
along every weak-graph edge $\mathbf{x} \to \mathbf{y}$ (with bound $-\|\mathbf{y} - \mathbf{x}\|_1$ for $\mathbf{w} = M^{-\mathsf T}\mathbf{1}$), so a cycle would have to strictly decrease a function back to its starting value.

**Connections without hyperbolicity.** For every Volterra–Lyapunov stable $A$, $\mathbf{x} \to \mathbf{y}$ in the connection graph iff $r_j(\mathbf{x}) > 0$ for $j \in J\setminus I$ and $r_i(\mathbf{y}) \le 0$ for $i \in I\setminus J$. Hence invasion graph $\subseteq$ connection graph $\subseteq$ weak graph, with equality when all equilibria are hyperbolic.

**Sharpness.** For $\mathbf{b} = \mathbf{1}$ and $A_c = -I - C$ with $C$ the cyclic matrix with entries $c$ on the superdiagonal and in the $(3,1)$ position, $A_c \in \mathcal{H}_-$ iff $0 \le c < 1$, while $A_c$ is Volterra–Lyapunov stable for $0 \le c < 2$. For $1 < c < 2$ the single-species equilibria form a heteroclinic cycle $\mathbf{e}_1 \to \mathbf{e}_2 \to \mathbf{e}_3 \to \mathbf{e}_1$ (rock–paper–scissors), so the dominance threshold $\rho(B) < 1$ cannot be relaxed to $\le 1$ in general.

## Expansion

The main inequality is a row comparison: if $h_i \ge 0$ or $(A\mathbf{h})_i \le 0$, then $(A\mathbf{h})_i \le -|a_{ii}||h_i| + \sum_{j\ne i}|a_{ij}||h_j|$. Applied to $\mathbf{h} = \mathbf{y} - \mathbf{x}$ between equilibria whose leaving species have nonpositive invasion rates at the target, it gives $r(\mathbf{y}) - r(\mathbf{x}) \le -M|\mathbf{y} - \mathbf{x}|$ componentwise. Pairing with $\mathbf{w}$ yields the strict decrease of $V_{\mathbf{w}}$ along weak edges, hence acyclicity of the largest graph and so of all three. Gradient structure then follows from the theory of dynamically gradient semiflows (an acyclic connection structure on finitely many equilibria inside a global attractor).

## Sources

- Matheus C. Bortolan, Piotr Kalita, José Antonio Langa and Rafael O. Moura, "Preventing cycles in Lotka--Volterra systems", arXiv:2611.26473 (2026), Section 1, Definition 1.2 and Theorem 1.3; Section 2, Lemma 2.1 and Theorem 2.3; Section 3, Theorem 3.2 and Proposition 3.5, <https://doi.org/10.48550/arXiv.2611.26473>.
