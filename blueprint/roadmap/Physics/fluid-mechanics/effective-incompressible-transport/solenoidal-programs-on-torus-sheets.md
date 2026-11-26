# Effective solenoidal programs on coding sheets of a flat torus

Use the torus $(\mathbb R/10\mathbb Z)^3$ with lift to $\mathbb R^3$ and the sheet $y\mapsto(y_1,y_2,2)$. Take two families $(P_i)$ and $(Q_i)$ of $N\ge0$ closed positive-width rational rectangles in $[2,3]^2$, separated by a positive distance within each family. Given positive rational ratios $r_{ij}$, require the diagonal map $D_i(y)=c(Q_i)+r_i\odot(y-c(P_i))$ to carry $P_i$ **onto** $Q_i$. No determinant-one condition is imposed on the sheet maps.

For every positive viscosity $\nu$ with a partial-recursive fast rational name (error $2^{-n}$ at precision $n$), there are globally smooth lifts $u,f$, both spatially $10\mathbb Z^3$-periodic, and a material flow $X$ with $X(0,a)=a$, with each trajectory continuous on $[0,\infty)$, and with $\partial_t X(t,a)=u(t,X(t,a))$ for $t\ge0$, using the right derivative at zero. For $t\ge0$ the velocity solves the incompressible forced Navier–Stokes equation from rest with pressure zero,

$$ \partial_t u+D_xu\,u=-\nabla p+\nu\Delta u+f,\qquad \operatorname{div}_x u=0,\qquad u(0,x)=0. $$

The force has spatial divergence zero and mean zero on $[0,10)^3$ at every time and is $1$-periodic in time. The velocity vanishes in a fixed open time collar around **every** integer (including negative integers in the lift), and $D_xu\,u=0$ everywhere. At time $1$, for every $i$ and every $y\in P_i$,

$$ X(1,(y,2))\equiv(D_i(y),2)\pmod{10\mathbb Z^3}. $$

The solution is unique in the following class with the same $f$: spatially periodic velocity and pressure, the same equation/divergence/zero initial datum, continuous on all slabs $[0,T]\times\mathbb R^3$, with the velocity time derivative (right at zero), all its spatial derivatives through second order, and the pressure spatial derivative existing and continuous there; the pressure has mean zero on each time slice. Thus the competitor has exactly velocity $u$ and pressure zero for all nonnegative times. For $N=0$ take $f=u=0$.

A single partial-recursive evaluator for the force takes the list of coordinate/time derivative directions, a code naming a spacetime point with error $2^{-n}$ in the coordinate product norm, and a positive rational tolerance. It returns a rational vector whose error in the coordinate product norm is strictly less than that tolerance. Separate partial-recursive functions in the derivative list return nonnegative rational global bounds on all mixed derivatives of $u$ and of $f$.

## Expansion

Construct the finite sheet shears and quantify their separated supports before closing the time period. Check forcing divergence and mean, vanishing advection and integer collars in the actual lift; prove the comparison-class energy identity and normalized pressure uniqueness. Verify force evaluation on arbitrary computable names and global derivative bounds, including the empty family.

## Sources

- OpenAI, [Comparator statement and definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SolenoidalSheetPrograms.lean#L17-L191) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/376.md).
- OpenAI, [Geometric Programs for Solenoidal Forcing](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Geometric-Programs-for-Solenoidal-Forcing-September-27-2026/manuscript.pdf) (September 27, 2026), accompanying preprint. The comparator above specifies the selected formal scope.
