# Rapidly decaying forced flow with a fixed-particle halting detector

Fix a positive real viscosity $\nu$ with a computable rational name of error $2^{-n}$. A machine is given by positive finite state and symbol counts, an initial state, a list of halting states and an optional instruction at table index $q\cdot(\text{alphabet size})+a$. All entries used on legal state/symbol pairs stay within the state and symbol ranges. The directions are $-1,0,1$ on a bilateral tape, initially containing the input word on nonnegative cells (zero is blank). A missing instruction enters a special halting state; halting states are absorbing. Use only well-formed machines with inputs in the alphabet. Halting means an iterate, including the zeroth, has reached a halting state.

There exist computable maps sending the machine/input code to programs for a force $f$ and velocity $U$, and **one** compact set $K\subset\mathbb R^3$ fixed before all machine/input pairs. For each valid pair there are $f,U$ smooth up to $t=0$ and supported in $K$ at every $t\ge0$. For every $J,l\in\mathbb N$ and spatial multiindex $\alpha$, the product

$$ (1+t+|x|)^J\,|\partial_t^l\partial_x^\alpha F(t,x)| $$

is bounded uniformly in $t\ge0,x\in\mathbb R^3$, for each $F=f,U$. Their programs give dyadic evaluations at rational points, local dyadic moduli on pairs of points in each closed spacetime ball of integer radius in $t\ge0$, and natural bounds for all these weighted derivatives. For evaluations at negative rational times only termination, not accuracy, is required.

The force and velocity are fields on $\mathbb R\times\mathbb R^3$. As an equality of fields on this entire domain, require $f=\partial_t^{[0,\infty)}U+D_xU\,U-\nu\Delta U$, where the time derivative is the totalized derivative within $[0,\infty)$; in particular it is the right derivative at zero. For negative times the within derivative is zero because the point is outside the closure of $[0,\infty)$; the global residual identity imposes no negative-time PDE admissibility or two-sided smoothness.

For $t\ge0$ the solution starts from rest, has zero pressure and is incompressible. On every finite closed time slab the solution is classical with $U\in C_tH_x^2\cap C_t^1L_x^2$, pressure in $C_tH_x^1$, and $U,\nabla U$ bounded. Every other classical zero-data solution with this force in the comparator class with $v\in C_tH_x^2\cap C_t^1L_x^2$, $p\in C_tH_x^1$ and bounded $v$ on each finite slab has exactly $v=U$ and $p=0$ on $t\ge0$. The classical derivatives (one time/through two spatial derivatives of velocity and one spatial derivative of pressure) are continuous on finite slabs, with right time derivative at zero.

For every starting point $a$ there is a unique material trajectory on $t\ge0$ with $X(a,0)=a$, $\partial_tX(a,t)=U(t,X(a,t))$ (right derivative at zero). From $a=(-1,0,0)$ its first coordinate is positive at some $t\ge0$ if and only if the machine halts on the input word.

## Expansion

Prove the finite-to-flow transition invariant and that trajectories cannot enter the detector unless a halting state is reached. Build the time sequence with one spatial support for every machine/input and effective weighted estimates for every derivative. Prove comparison uniqueness in the weaker competitor class, which does not impose a first-derivative bound on the competing velocity.

## Sources

- OpenAI, [Comparator statement and definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/NavierStokesAlternating.lean#L10-L241) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/376.md).
- OpenAI, [Computation under Rapidly Vanishing Navier–Stokes Forcing](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Computation-under-Rapidly-Vanishing-Navier-Stokes-Forcing-September-27-2026/manuscript.pdf) (September 27, 2026), accompanying preprint. The comparator above specifies the selected formal scope.
