# Matching-types predator-prey dynamics and accumulating invasion cycles

**Individual-based model.** Prey of types $i\in\{0,1\}$ and predators of types $j\in\{0,1\}$. Each prey gives birth at rate $b$ and dies at rate $d+c_KN+p_KH_i$ ($N$ total prey, $H_i$ the matching predators); each predator gives birth at rate $\beta+\rho_KN_j$ (prey of the matching type) and dies at rate $\delta+\gamma_KH$ ($H$ total predators). Types are otherwise neutral: competition does not distinguish types. Offspring switch type (mutate) with small probabilities $v_K$ (prey) and $\vartheta_K$ (predators). Prey populations are of order $K$ and predator populations of order $K^m$.

**Large population limit.** Rescaled counts converge on finite time intervals to

$$\dot n_i=n_i\big(b-d-c(n_0+n_1)-ph_i\big),\qquad \dot h_i=h_i\big(\beta-\delta-\gamma(h_0+h_1)+\rho n_i\big).$$

With $\bar n=(b-d)/c$ and $\bar h=(\beta-\delta)/\gamma$, the equilibria are extinction, lines of prey-only and predator-only two-type states, non-matching pairs $(\bar n,0,0,\bar h)$ (prey and predator of different types, which do not interact), matching pairs $(\hat n,0,\hat h,0)$, and full coexistence $n_0=n_1=n^*$, $h_0=h_1=h^*$ with

$$n^*=\frac{2\gamma(b-d)-p(\beta-\delta)}{p\rho+4c\gamma},\qquad h^*=\frac{\rho(b-d)+2c(\beta-\delta)}{p\rho+4c\gamma},$$

feasible iff $-\frac{\rho}{2\gamma}\bar n<\bar h<\frac{2c}p\bar n$; under these conditions every positive solution converges to it. The parameter regimes, organized by the position of $\bar h$ relative to $\bar n$, determine which equilibria exist and attract.

**Theorem (mutation time scale).** When mutations are rare, on the time scale $t\log K$ the exponents $\log(\text{population size})/\log K$ of the four types converge in probability to explicit piecewise-linear trajectories, while the macroscopic state jumps between deterministic equilibria. The dynamics are **eco-evolutionary cycles**: a prey type escapes its matching predator and invades, the matching predator type then invades, which favors the other prey type, and so on.

**Theorem (accumulation).** When four-type coexistence is possible (for example $\hat n>0$ and $\bar h>0$), successive invasion times satisfy $s_{2(k+2)}-s_{2(k+1)}\le\frac{\bar r\hat\varrho}{\hat r\bar\varrho}(s_{2(k+1)}-s_{2k})$ with ratio below 1, so the cycles accumulate at a finite time $S_*$ at which all four exponents tend to 1 (all types macroscopic). In a variant with slightly unequal intra- and inter-type competition, all four populations remain macroscopic after $S_*$ and converge to the coexistence equilibrium.

## Depends on

- [Lotka-Volterra predator-prey model](../lotka-volterra-predator-prey-model/README.md)

## Expansion

The individual-based process is a multitype birth-death process with immigration (mutation feeds each type from the other). Convergence to the ODE on bounded time intervals follows from Ethier-Kurtz. Small subpopulations are compared with linear branching processes with exponentially growing immigration, whose log-size scaled by $\log K$ converges to $(\beta+rs)\vee(c+as)$ (Champagnat-Méléard-Tran). Each phase of the limit is thus a resident deterministic equilibrium plus rare types growing or shrinking at linear rates on the log scale, with fitness given by invasion rates at the current equilibrium. The contraction of phase lengths comes from the ratio of growth and decay rates of invaders at the two alternating equilibria, and stability of the coexistence equilibrium controls behavior after accumulation. The symmetric neutral-competition case makes this analysis delicate because some equilibria are non-isolated (lines of equilibria).

## Sources

- M. Costa, P. Czuppon, R. Forien, "Eco-evolutionary cycles in a matching type predator-prey interaction", arXiv:2609.04834 (2026), Section 2 (individual-based model, Lemma 2.1, Propositions 2.2-2.7), Section 3 (Definitions 3.1-3.2, Theorems 1-2), Section 4 (Proposition 4.1, Corollary 4.2, Proposition 4.3) and Sections 5-6, <https://doi.org/10.48550/arXiv.2609.04834>.
