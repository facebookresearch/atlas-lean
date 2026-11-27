# Invasion graph of an ecological community

**Model.** Consider $n$ interacting species with densities $x = (x_1, \dots, x_n) \ge 0$ and auxiliary
variables $y \in Y$ (population structure, seasonal forcing, abiotic factors):

$$\frac{dx_i}{dt} = x_i f_i(z), \quad i \in [n] = \{1, \dots, n\}, \qquad \frac{dy}{dt} = g(z), \qquad z = (x, y),$$

on $K = [0, \infty)^n \times Y$, with extinction set $K_0 = \{ z \in K : \prod_i x_i = 0 \}$. Assume
(A1) $x_i f_i$ and $g$ are locally Lipschitz, and (A2) the system is dissipative, with a compact
global attractor $\Gamma$; write $\Gamma_0 = \Gamma \cap K_0$.

**Invasion growth rates.** For $S \subseteq [n]$ let $F(S) = \{ (x, y) \in K : x_j > 0 \iff j \in S \}$.
For an ergodic invariant probability measure $\mu$, its species support $S(\mu)$ is the smallest set
with $\mu(F(S(\mu))) = 1$, and the invasion growth rate of species $i$ is

$$r_i(\mu) = \int_K f_i(z)\, \mu(dz),$$

the long-run per-capita growth rate of $i$ when introduced at vanishing density into the dynamics
described by $\mu$ (by Birkhoff's ergodic theorem).

**Lemma.** For every ergodic $\mu$, $r_i(\mu) = 0$ for all resident species $i \in S(\mu)$.

**Invasion scheme and graph.** Assume (A3a) $r_j(\mu) \neq 0$ for every ergodic $\mu$ supported on
$\Gamma_0$ and every $j \notin S(\mu)$, and (A3b) $\operatorname{sgn} r_j(\mu) = \operatorname{sgn} r_j(\nu)$
whenever $S(\mu) = S(\nu)$. Set $r_i(S) = \operatorname{sgn} r_i(\mu)$ for $S = S(\mu)$, and let
$\mathcal{S}$ be the set of proper subcommunities $S \subsetneq [n]$ arising as $S(\mu)$ (it always
contains $\emptyset$). The **invasion scheme** is the sign table $\{ r_i(S) \}_{S \in \mathcal{S},\, i \in
[n]}$. The **invasion graph** has vertex set $\mathcal{S}$ and a directed edge $S \to T$ iff

$$S \neq T, \qquad r_j(S) > 0 \ \text{for all } j \in T \setminus S, \qquad r_i(T) < 0 \ \text{for all } i \in S \setminus T .$$

If some trajectory in $\Gamma_0$ has its $\alpha$-limit set in $F(S)$ and its $\omega$-limit set in
$F(T)$ with $T \ne S$, then $S \to T$ is an edge.

## Expansion

Linearizing the equation of a rare species $i$ along a trajectory gives
$\log(\tilde x_i(t)/\tilde x_i(0)) = \int_0^t f_i(z \cdot s)\, ds$, whose time average converges to
$r_i(\mu)$ for $\mu$-almost every initial condition. For a resident species, Poincaré recurrence
returns the trajectory infinitely often to a compact subset of $F(S(\mu))$ where $x_i$ is bounded
above and away from zero, so the time-averaged growth rate, and hence $r_i(\mu)$, must vanish. The
edge conditions encode the possible community transitions: every species gained can invade the
starting community, and every species lost cannot reinvade the end community. For Lotka–Volterra
systems $f(x) = Ax + b$ with at most one equilibrium in each face, time averages along trajectories
converge to that equilibrium $x^*$, so $r_i(S) = \operatorname{sgn}\bigl((A x^*)_i + b_i\bigr)$ and the
invasion graph is computed by solving linear systems, one per face.

## Sources

- J. Hofbauer, S. J. Schreiber, "Permanence via invasion graphs: incorporating community assembly
  into modern coexistence theory", Journal of Mathematical Biology 85 (2022) 54, Section 2, model
  (1), assumptions A1-A3, Lemma 1, definitions of the invasion scheme and invasion graph, Remark 1,
  and Section 3 (Lotka–Volterra systems), <https://doi.org/10.1007/s00285-022-01815-2> (PMC9579112).
