# Graphon-type continuum limit of plant–pollinator networks and concentration of stationary states

**Model.** A community of $n$ plant species with generalism traits $x^i \in [0,1]$ and $m$ pollinator species with traits $y^j \in [0,1]$ interacts through a random bipartite graph: conditionally on the traits, plant $i$ and pollinator $j$ are linked independently with probability $\phi(x^i, y^j)$, for a Lipschitz $\phi : [0,1]^2 \to [0,1]$, and a link carries a harvesting coefficient $c_{ij} \approx c(x^i, y^j)$ (scaled by $1/n$). Individuals reproduce and die at rates depending on the resource obtained from their partners: the per-capita growth rates are $g^P(R) = b^P(R) - d^P(R)$ for plants and $g^A(R) = b^A(R) - d^A(R)$ for pollinators, with intra-guild competition kernels $k$ and $h$. Abundances are of order $K$ (carrying capacity).

**Theorem (two-step limit).**
1. *Large abundances.* For fixed $n, m$, as $K \to \infty$ the rescaled abundances converge a.s. uniformly on $[0,T]$ to the Lotka–Volterra-type ODE system

$$\dot P^i = P^i\Big[g^P\Big(\sum_{j \sim i} c_{ij} A^j\Big) - \sum_\ell k_{i\ell}P^\ell\Big], \qquad \dot A^j = A^j\Big[g^A\Big(\sum_{i \sim j} c_{ij} P^i\Big) - \sum_\ell h_{j\ell}A^\ell\Big],$$

and fluctuations of order $\sqrt{K}$ satisfy a central limit theorem (Gaussian linear SDE).
2. *Many species.* If $m/n \to 1$ and the initial empirical measures $\frac1n\sum_i P^i_0\delta_{x^i}$, $\frac1m\sum_j A^j_0\delta_{y^j}$ converge weakly to bounded continuous densities $\bar p_0$, $\bar a_0$ (with uniformly bounded total masses), then as $n, m \to \infty$ the empirical measures converge in law in $C([0,T], \mathcal{M}_F([0,1])^2)$ to the unique deterministic solution, with densities $\bar p_t$, $\bar a_t$, of the integro-differential system

$$\partial_t \bar p_t(x) = \bar p_t(x)\Big[g^P\Big(\int_0^1 \psi(x,y)\bar a_t(y)\,dy\Big) - k \star \bar p_t(x)\Big], \qquad \partial_t \bar a_t(y) = \bar a_t(y)\Big[g^A\Big(\int_0^1 \psi(x,y)\bar p_t(x)\,dx\Big) - h \star \bar a_t(y)\Big],$$

with interaction kernel $\psi = c\,\phi$.

**Proposition (no density stationary states).** Suppose $k$ and $h$ are constant and $\psi(x_0, \cdot)$ and $\psi(\cdot, y_0)$ are continuous and increasing for every $x_0, y_0$. Then the continuum system has no non-null stationary state with densities with respect to Lebesgue measure. Every non-null stationary state is a pair of atomic measures $\bar P^\infty = \bar p_1\delta_{\bar x_1} + \bar p_2\delta_{\bar x_2}$, $\bar A^\infty = \bar a_0\delta_{\bar y_0}$ with $\bar p_1, \bar a_0 > 0$, $\bar p_2 \ge 0$, satisfying

$$g^P(\bar a_0\psi(\bar x_1, \bar y_0)) = g^P(\bar a_0\psi(\bar x_2, \bar y_0)) = k(\bar p_1 + \bar p_2), \qquad g^A\big(\bar p_1\psi(\bar x_1,\bar y_0) + \bar p_2\psi(\bar x_2, \bar y_0)\big) = h\bar a_0.$$

## Proof sketch

Step 1 is a standard law of large numbers for density-dependent jump processes driven by Poisson point measures. In step 2 the sums $\frac1n\sum_{j\sim i}c_{ij}A^j$ are averages over an inhomogeneous random graph, which concentrate on $\int \psi(x^i, y)\bar a(y)\,dy$, a graphon limit. At a stationary state each surviving trait must have zero growth; with constant competition the plant condition reads $g^P(\int\psi(x,y)\,\bar A^\infty(dy)) = k\|\bar P^\infty\|$ on the support of $\bar P^\infty$, and strict monotonicity of $\psi$ in each variable forces the zero set to be finite, so mass concentrates on at most two plant traits and one pollinator trait.

## Sources

- Sylvain Billiard, Hélène Leman, Thomas Rey and Viet Chi Tran, "Continuous limits of large plant-pollinator random networks and some applications", *MathematicS In Action* 14 (2026), 23–54, <https://doi.org/10.5802/msia.42>. Preprint version: arXiv:2201.05219 (2022), Propositions 2.1, 3.2 and 4.5, Lemma 4.4, <https://doi.org/10.48550/arXiv.2201.05219>.
