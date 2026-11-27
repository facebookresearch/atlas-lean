# Fixed points of the collective growth map

**Within-collective ecology.** Two particle types (red $0$, blue $1$) grow inside a collective according to the competitive Lotka–Volterra system

$$\frac{dN_0}{dt} = r_0 N_0\big(1 - a_{00}N_0 - a_{01}N_1\big), \qquad \frac{dN_1}{dt} = r_1 N_1\big(1 - a_{10}N_0 - a_{11}N_1\big),$$

with maximal growth rates $r_0 > r_1 > 0$ and competition coefficients $a_{ij} \ge 0$ (carrying-capacity scale set to $1$). Write $N = N_0 + N_1$ and colour $x = N_0/N$.

**Growth map.** A collective is founded with $B$ particles of colour $\phi \in [0,1]$ (bottleneck size $B > 0$) and grows for a time $T > 0$. The growth map is

$$G_\theta(\phi, T, B) = x(T) \quad \text{for the solution with } N(0) = B,\ x(0) = \phi,$$

where $\theta = (r_0, r_1, A)$. Ignoring dilution noise, the colour of successive collective generations follows the iteration $\phi_{k+1} = G_\theta(\phi_k, T, B)$.

**Proposition.**

1. *Fixed points.* $G_\theta(0, T, B) = 0$ and $G_\theta(1, T, B) = 1$ for all $\theta$. If $\phi = 0$ and $\phi = 1$ have the same stability under the iteration, $G_\theta$ has at least one fixed point in $(0,1)$.
2. *Quasi-exponential growth.* If $T$ is close to $0$ and $B\,a_{\max} \ll 1$ with $a_{\max} = \max_{i,j} a_{ij}$, then $0$ and $1$ are the only fixed points, $\phi = 1$ (all fast-growing red) is stable and $\phi = 0$ unstable.
3. *Saturating growth.* As $T \to \infty$, the fixed points of $G_\theta$ and their stability are those of the colour at the Lotka–Volterra equilibria: red alone ($x^* = 1$) is stable iff $a_{00} < a_{10}$; blue alone ($x^* = 0$) is stable iff $a_{11} < a_{01}$; and if $a_{11} > a_{01}$ and $a_{00} > a_{10}$ there is a stable coexistence colour

    $$x^* = \frac{a_{11} - a_{01}}{\operatorname{Tr}(A) - \operatorname{CoTr}(A)}, \qquad \operatorname{Tr}(A) = a_{00} + a_{11},\ \operatorname{CoTr}(A) = a_{10} + a_{01}.$$

4. *Bifurcations.* Between these limits the monochromatic fixed points change stability through transcritical bifurcations along curves in the $(T, B)$ plane that can be computed exactly by linearising $G_\theta$ at $\phi = 0$ and $\phi = 1$.

An interior stable fixed point of $G_\theta$ means that offspring collectives founded with a perturbed colour return toward the parental colour within a generation: heredity at the collective level emerges from particle ecology.

## Expansion

In the colour coordinates, $\dot x = x(1-x)\,h(x, N)$ for a function $h$ given by the difference of per-capita growth rates of the two types, so $x \equiv 0$ and $x \equiv 1$ are invariant, giving item 1; continuity of $G_\theta$ on $[0,1]$ and equal stability at both ends force a crossing of the diagonal (intermediate value theorem). For short growth and small founding size, competition is negligible, $N_i(T) \approx N_i(0)e^{r_iT}$, so $G_\theta(\phi) = \phi e^{r_0T}/(\phi e^{r_0T} + (1-\phi)e^{r_1T}) > \phi$ on $(0,1)$ and red fixes. For long growth, $x(T)$ converges to the colour of the attracting Lotka–Volterra equilibrium; solving $1 = a_{00}N_0 + a_{01}N_1 = a_{10}N_0 + a_{11}N_1$ gives $N_0^* \propto a_{11} - a_{01}$, $N_1^* \propto a_{00} - a_{10}$ and hence $x^*$. Under selection for an intermediate collective colour, particle traits evolve from the regime of item 2 (maintenance only by stochastic correction and purging) toward item 3 with an interior fixed point near the target (developmental correction).

## Sources

- G. Doulcier, A. Lambert, S. De Monte, P. B. Rainey, "Eco-evolutionary dynamics of nested Darwinian populations and the emergence of community-level heredity", eLife 9 (2020) e53433, Results (Figure 5, growth function) and Appendix 2 (competitive Lotka–Volterra model, Equation 1; growth function, Definition 2; Propositions 1–4 with proofs; Appendix 2—figure 3), <https://doi.org/10.7554/eLife.53433> (PMC7440921).
