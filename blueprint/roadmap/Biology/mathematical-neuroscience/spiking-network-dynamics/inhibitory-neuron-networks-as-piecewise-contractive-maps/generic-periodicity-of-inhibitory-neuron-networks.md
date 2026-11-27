# Generic periodicity of networks of inhibitory neurons via piecewise contractive maps

**Abstract setting.** Let $B$ be a compact region of a finite-dimensional manifold with a finite partition $B = B_1 \cup \dots \cup B_n$, and let $F : B \to B$ be **piecewise continuous** ($F|_{B_i} = f_i$ continuous on each piece). Call $F$ **locally contractive** if there are a distance and constants $0 < \lambda < 1$ with $\mathrm{dist}(f_i(V), f_i(W)) \le \lambda\,\mathrm{dist}(V,W)$ for all $V, W \in B_i$ and all $i$, and say $F$ has the **separation property** if it maps the different continuity pieces homeomorphically onto pairwise disjoint sets. $F$ is **eventually periodic with persistent limit cycles** if every orbit converges to one of finitely many periodic orbits and these persist under small perturbations of $F$.

**Theorem (abstract).** Let $F$ be a locally contractive piecewise continuous map with the separation property. Then, generically (for an open and dense set of such maps), $F$ is eventually periodic with a finite number of persistent limit cycles.

**Neural model.** Consider $n \ge 3$ inhibitory neurons with state $V = (V_1, \dots, V_n) \in Q = [-1,1]^n$. Between spikes each potential obeys

$$\frac{dV_i}{dt} = \gamma_i(V_i), \qquad \gamma_i \in C^1([-1,1]),\quad \gamma_i > 0,\quad \gamma_i' < 0 \text{ on } [-1,1]\qquad\text{(1)}$$

(pacemaker neurons with dissipative free evolution, e.g. $\gamma_i(V) = \beta_i - \alpha_iV$ with $0 < \alpha_i < \beta_i$). When a single neuron $i$ reaches the threshold $1$, it resets and inhibits all the others instantaneously:

$$V_i \mapsto 0, \qquad V_j \mapsto \max\{-1,\ V_j - H_{ij}\}\quad (j \ne i),\qquad\text{(6)–(7)}$$

with constants $H_{ij} > 0$, so the inhibitory graph is complete, $\epsilon_0 = \min_{i\ne j}H_{ij} > 0$ (8). With $\Gamma = \min_i\min_{V\in[1/4,3/4]}|\gamma_i'(V)|$, assume the relatively large dissipation conditions

$$\max_{i\ne j}H_{ij} < \frac14, \qquad \max_{i,j}|\gamma_i(3/4) - \gamma_j(3/4)| < \frac{\Gamma}{4}, \qquad \frac{\max_{i\ne j}H_{ij}}{\min_{i\ne j}H_{ij}} - 1 < \frac{\Gamma}{4\max_i\gamma_i(3/4)}.\qquad\text{(9)–(11)}$$

**Theorem (network).** Under these hypotheses there is a Poincaré section $B^+ = \bigcup_i B_i^+$, homeomorphic to an $(n-1)$-dimensional compact ball and made of the states in which some neuron has just been reset ($V_i = 0$), reached from every initial state, such that the return map $F : B^+ \to B^+$:
1. is piecewise continuous, the piece $B_i^+$ being determined by which neuron fires next;
2. is injective on each piece and has the separation property;
3. is uniformly, but not infinitely, contractive on each piece: there are $0 < \sigma < \lambda < 1$ and a distance with $\sigma\,\mathrm{dist}(V,W) \le \mathrm{dist}(f_i(V), f_i(W)) \le \lambda\,\mathrm{dist}(V,W)$.

Consequently a topologically generic network of three or more inhibitory neurons has periodic spiking behaviour, with finitely many limit cycles that persist under small perturbations of the network structure.

## Proof sketch

Contraction on each piece squeezes every orbit segment that stays in one sequence of pieces, so orbits can only be complicated by repeatedly hitting the discontinuity set. The separation property means the images of the pieces are disjoint compact sets, and generically the atoms $F^k(B_{i_1}) \cap \dots$ eventually avoid the discontinuity boundaries; once they do, each surviving atom is mapped into itself by some iterate, which is a contraction there and has a unique attracting periodic point. Inhibition is what produces the separation property: after neuron $i$ fires, all others are pushed down, so the post-spike states of different firing neurons cannot coincide.

## Sources

- E. Catsigeras, A. Rovella and R. Budelli, "Contractive piecewise continuous maps modeling networks of inhibitory neurons", *International Journal of Pure and Applied Mathematics* 61(4) (2010), 381–407. Preprint version: arXiv:0805.2695 (2008), Theorems 2.4, 2.7, 2.9, 2.11, Corollary 2.13 and Theorem 4.1, <https://doi.org/10.48550/arXiv.0805.2695>.
