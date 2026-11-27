# Finite-machine halting detected by a fixed fluid particle

A machine here has finite state and symbol sets of sizes $s+1$ and $a+1$, a selected initial state and blank symbol, and a deterministic partial table on state/symbol pairs. A defined instruction replaces the symbol, changes state and moves the head left, right or not at all on a bilateral integer tape. At time zero the finite input word occupies consecutive nonnegative cells starting at zero; all other cells are blank and the head is at zero. Halting means reaching a configuration in finitely many steps, possibly zero, with no next instruction.


There exist simultaneously three families of velocity-shaped fields $U_{M,w},f_{0,M,w},f_{1,M,w}$ and a family of material flows $X_{M,w}$ on $\mathbb R^3$, indexed by each machine $M$ and valid input word $w$. There is a $1$-periodic field $R_M$ for each machine, independent of $w$, with $U_{M,w}(t,x)=R_M(t,x)$ for $t\ge1$. For every $M,w$, suppress the indices. The fields $U,f_0,f_1$ are smooth for $t\ge0$ and share a compact **spatial** support for all nonnegative times for this pair. All mixed derivatives of $U$ are bounded there. The material flow solves $X(0,a)=a$, $\partial_tX(t,a)=U(t,X(t,a))$ for $t\ge0$ (right derivative at zero), and

$$ (\exists t\ge0:\ X(t,(4,0,0))\in(-1,2)^3)\quad\Longleftrightarrow\quad M\text{ halts on }w. $$

For all real $\nu>0$ the **same** $U$ solves the incompressible Navier–Stokes equation from rest with pressure zero and force $f=f_0+\nu f_1$, where $f_0=\partial_tU+D_xU\,U$ and $f_1=-\Delta U$. The force is smooth with bounded mixed derivatives and is $1$-periodic for $t\ge1$. Both the displayed velocity (with zero pressure) and the uniqueness comparison are in the class with velocity in $C_tH_x^2\cap C_t^1L_x^2$, velocity and its first spatial derivatives bounded on every finite time slab, and pressure in $C_tH_x^1$ after subtracting a time-dependent constant. Any smooth zero-data solution of the same forced equation in that class has velocity $U$ and pressure spatially constant at each nonnegative time.

The three families have computable codes, uniform in the finite table and input, for their mixed derivatives at nonnegative rational spacetime points to coordinatewise error $2^{-m}$. They also give computable global natural derivative bounds and support radii for each encoded pair. The combined force has computable dyadic evaluation and derivative bounds for computable $\nu$, and for **every** fast rational name of $\nu$ it has such evaluation and bounds relative to the oracle of that name. These effective clauses do not decide the halting event.

## Proof depends on

- [Volume-preserving routing of solid boxes](volume-preserving-routing-of-solid-boxes.md)

## Expansion

Model the bilateral tape transition and prove simulation and the exact halt-to-detector equivalence. Separate input loading from the repeated machine-only field and prove quantitative derivative and support bounds after gluing. In the comparison class derive the velocity energy inequality and spatial constancy of pressure; use the affine dependence to prove the relativized and absolute force evaluators.

## Sources

- OpenAI, [Comparator statement and definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BalancedThreeStack.lean#L20-L235) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/376.md).
- OpenAI, [Incompressible Box Transport and Finite Computation](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Incompressible-Box-Transport-and-Finite-Computation-September-27-2026/manuscript.pdf) (September 27, 2026), accompanying preprint. The comparator above specifies the selected formal scope.
