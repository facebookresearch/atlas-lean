# Strong-inactivation limit of the conditional mean first passage time

Discretize the cytosol on a cubic grid of mesh width $h$: let $\mathcal{C}_h$ be the cytosolic voxels, $\mathcal{N}_h$ the nuclear voxels (absorbing), and $\Delta_h$ the six-nearest-neighbor discrete Laplacian with reflecting conditions at the cell membrane and organelle voxels. The active-molecule density solves $\frac{d}{dt}p_{\lambda,h} = D\Delta_h p_{\lambda,h} - \lambda p_{\lambda,h}$ with initial density $g_h$ supported on a set $\mathcal{G}_h$ of voxels next to the cell membrane. Let $d = d(\mathcal{G}_h,\mathcal{N}_h)$ be the shortest nearest-neighbor path length (graph distance) from $\mathcal{G}_h$ to the nucleus through cytosolic voxels, and let $f_h(t)$, $Z_{\lambda,h}$ and $\langle T_{\lambda,h}\rangle$ be the arrival density, arrival probability and conditional mean arrival time.

**Theorem.** (i) Mass is conserved by the first $d-1$ Laplacian powers:

$$\sum_{V_i \in \mathcal{C}_h}\bigl((\Delta_h)^k g_h\bigr)(x_i) = 0, \qquad 1 \leq k \leq d - 1 .$$

(ii) Hence $f_h(t) \sim -h^3 \dfrac{D^d t^{d-1}}{(d-1)!}\displaystyle\sum_{V_i \in \mathcal{C}_h}\bigl((\Delta_h)^d g_h\bigr)(x_i)$ as $t \to 0$, and, for $d > 1$,

$$Z_{\lambda,h} \sim -\frac{h^3 D^d}{\lambda^d}\sum_{V_i \in \mathcal{C}_h}\bigl((\Delta_h)^d g_h\bigr)(x_i), \qquad \langle T_{\lambda,h}\rangle = -\frac{d}{d\lambda}\log Z_{\lambda,h} \sim \frac{d(\mathcal{G}_h,\mathcal{N}_h)}{\lambda}, \qquad \lambda \to \infty .$$

(iii) Comparing the true geometry with organelles as obstacles ("phys") to the same cell with organelles removed ("n.o."),

$$\frac{\langle T_{\lambda,h}\rangle_{\mathrm{phys}}}{\langle T_{\lambda,h}\rangle_{\mathrm{n.o.}}} \to \frac{d(\mathcal{G}_h,\mathcal{N}_h)_{\mathrm{phys}}}{d(\mathcal{G}_h,\mathcal{N}_h)_{\mathrm{n.o.}}} \geq 1 \qquad (\lambda \to \infty).$$

Strong inactivation therefore buffers the slowing effect of organelle barriers down to the ratio of shortest-path distances; for a fixed starting voxel whose shortest path to the nucleus is unobstructed, the effect of organelles on the conditional mean arrival time disappears entirely in the limit. The analogous continuum statement, with geodesic distances from the support of the initial density to the nucleus, is stated as a conjecture.

## Depends on

- [Conditional first passage time decreases with the inactivation rate](conditional-first-passage-time-decreases-with-inactivation-rate.md)

## Expansion

Write $f_h(t) = -\frac{d}{dt}\sum_i p_h(x_i,t)h^3$ and expand $e^{tD\Delta_h}g_h$ in powers of $t$: $f_h(t) = -h^3\sum_{n \geq 0}\frac{D^{n+1}t^n}{n!}\sum_i((\Delta_h)^{n+1}g_h)(x_i)$. Each application of $\Delta_h$ spreads mass by one voxel, so $(\Delta_h)^k g_h$ has no mass next to the nucleus until $k = d-1$; before that the Laplacian only moves mass within the cytosol, and its total is conserved, which is item (i). The first nonzero term is therefore of order $t^{d-1}$, and since $e^{-\lambda t}$ localizes the Laplace integral $Z_{\lambda,h} = \int_0^\infty e^{-\lambda t}f_h(t)\,dt$ at small $t$, Watson's lemma turns $t^{d-1}/(d-1)!$ into $\lambda^{-d}$. Taking the logarithmic derivative gives $d/\lambda$. Removing organelles only adds cytosolic voxels, so distances can only shrink, giving a limiting ratio $\geq 1$. Numerically the limit needs very large $\lambda$ and is not approached monotonically, so its value lies in explaining why inactivation filters out long paths rather than in the predicted scaling.

## Sources

- J. Ma, M. Do, M. A. Le Gros, C. S. Peskin, C. A. Larabell, Y. Mori, S. A. Isaacson, "Strong intracellular signal inactivation produces sharper and more robust signaling from cell membrane to nucleus", *PLoS Computational Biology* 16(11) (2020) e1008356. Results, "Large inactivation rate asymptotics": Eq. 15, Theorem 2, Eqs. 16–18 (asymptotic formula proved as Theorem 3 of S1 Text, with Lemma 1 there); Discussion, "Conjectures and Open Problems". <https://doi.org/10.1371/journal.pcbi.1008356>. PMCID: PMC7704053.
