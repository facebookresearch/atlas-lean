# Global classical relativistic Vlasov–Maxwell solutions in three dimensions

Write $\widehat v=v/\sqrt{1+\|v\|^2}$, $\rho_f(t,x)=\int f(t,x,v)\,dv$ and $j_f(t,x)=\int f(t,x,v)\widehat v\,dv$ on three-dimensional Euclidean position and momentum space. Initial $f_0$ is everywhere nonnegative, smooth and compactly supported. Initial $E_0,B_0$ are smooth with bounded derivatives of every order, including order zero, and are square-integrable. Require $\operatorname{div}E_0=\rho_{f_0}$ and $\operatorname{div}B_0=0$.

There are $f,E,B$ taking these data at $t=0$. On $t\ge0$ they are $C^1$, with time derivatives from the closed half-line, and solve

$$\partial_tf+\widehat v\cdot\nabla_x f+(E+\widehat v\times B)\cdot\nabla_v f=0,\qquad
\partial_tE-\operatorname{curl}B=-j_f,\qquad
\partial_tB+\operatorname{curl}E=0,$$

with $\operatorname{div}E=\rho_f$ and $\operatorname{div}B=0$. The density is nonnegative, and on each $[0,T]$, $T\ge0$, a single compact set in phase space contains all its spatial/momentum supports. Each field has a continuous-in-time $L^2(\mathbb R^3)$ representative on $[0,\infty)$ agreeing with its time slice almost everywhere. The solution is smooth on each closed finite time slab. Any other solution obeying the classical $C^1$, positivity, support, energy-continuity, equation and initial-data clauses agrees pointwise for $t\ge0$; it need not be assumed smooth.

## Depends on

- Classical derivatives on closed half-spaces and the compact phase-support and $L^2$-field conditions above.

## Proof depends on

- Relativistic characteristic local existence, persistence of the Gauss constraints, a continuation estimate preventing finite-time blow-up, and classical uniqueness in the stated class.

## Expansion

Separate local existence, finite-horizon momentum and position bounds, continuation of all derivatives, and uniqueness among classical solutions. The energy-continuity side condition does not supply the required global continuation estimate.

## Sources

- OpenAI, [VlasovMaxwell comparator, global_classical_solution](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/VlasovMaxwell.lean#L103-L107).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/362.md).
