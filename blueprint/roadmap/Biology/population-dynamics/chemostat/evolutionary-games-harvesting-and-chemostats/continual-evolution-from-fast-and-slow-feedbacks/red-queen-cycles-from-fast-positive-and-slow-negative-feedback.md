# Red Queen cycles from a fast positive and a slow negative feedback

**Setting (two phenotypes, constant population size).** A single species consists of two phenotypes $A$ and $B$ with $A+B$ constant, and $R = A/(A+B) \in [0,1]$ is the frequency of $A$. An external factor $\varphi \in [0,1]$ (a predator, a host defense, an abiotic compound) is driven mainly by $A$ and harms $A$. The eco-evolutionary dynamics are

$$
\frac{dR}{dt} = f(R,\varphi) + \epsilon_m\, g(R), \qquad \frac{d\varphi}{dt} = \epsilon_e\, h(R,\varphi),
$$

with $f,g,h$ continuously differentiable and $\epsilon_m,\epsilon_e > 0$ the (small) time scales of mutation and of the feedback variable. Assume

- **(EXT)** $f(0,\varphi) = f(1,\varphi) = 0$ (an extinct phenotype does not reproduce);
- **(MUT)** $g$ is decreasing in $R$, $g(0) > 0$ and $g(1) < 0$ (mutation pushes away from both boundaries). The source prints $g(1) < 1$; since $f(1,\varphi) = 0$ by (EXT), $dR/dt = \epsilon_m g(1)$ at $R = 1$, so a frequency $R$ stays in $[0,1]$ only if $g(1) \le 0$, and mutation pushes $R$ off $1$ only if $g(1) < 0$;
- **(PF, fast positive feedback)** $f$ is strictly decreasing in $\varphi$ and $\partial f / \partial R > 0$;
- **(NF1)** $h$ is decreasing in $\varphi$ and increasing in $R$;
- **(NF2, slow dominating negative feedback)** there are $0 < \varphi_{--} < \varphi_{++} < 1$ such that $f > 0$ on $(0,1)$ whenever $\varphi < \varphi_{--}$ and $f < 0$ on $(0,1)$ whenever $\varphi > \varphi_{++}$; and for each $\varphi \in (0,1)$, $h(R,\varphi) > 0$ for $R$ close to $1$ and $h(R,\varphi) < 0$ for $R$ close to $0$.

**Theorem (continual evolution).** There is a rectangle $[a,b] \times [c,d] \subset (0,1)^2$ containing all fixed points such that, for $\epsilon_e$ and $\epsilon_m$ sufficiently small, almost every orbit converges to a periodic orbit that intersects both $\{R > b\}$ and $\{R < a\}$. Thus the trait frequency oscillates indefinitely between near-fixation of $A$ and near-fixation of $B$ (Red Queen dynamics with a single evolving trait), instead of settling at an evolutionary equilibrium.

**Variable population size.** The same conclusion holds without $A + B$ constant, for

$$
\frac{dA}{dt} = A\, f_A(A,B,\varphi) + \epsilon_m g(A,B), \quad \frac{dB}{dt} = B\, f_B(A,B,\varphi) - \epsilon_m g(A,B), \quad \frac{d\varphi}{dt} = \epsilon_e h(A,B,\varphi),
$$

with $f_A, f_B, g, h$ continuously differentiable, the total population bounded above and below, $R = A/(A+B)$, and the following assumptions (the source's SI Section 4.2):

- **(PF)** $\big(\partial_A - \partial_B\big)f_A > 0$ and $\big(\partial_B - \partial_A\big)f_B > 0$ everywhere;
- **(USV1)** for fixed $B, \varphi$ there is a unique $A_0 = \eta_A(B,\varphi) \ge 0$ with $f_A > 0$ for $0 \le A < A_0$ and $f_A < 0$ for $A > A_0$;
- **(USV2)** for fixed $A, \varphi$ there is a unique $B_0 = \eta_B(A,\varphi) \ge 0$ with $f_B > 0$ for $B < B_0$ and $f_B < 0$ for $B > B_0$;
- **(NF1)** $f_A - f_B$ decreases with $\varphi$, and $\big(\partial_A - \partial_B\big)h > 0$;
- **(NF2)** there are $0 < \varphi_{--} < \varphi_{++} < 1$ with $f_B > f_A$ whenever $\varphi > \varphi_{++}$ and $f_A > f_B$ whenever $\varphi < \varphi_{--}$;
- **(Tr)** $h > 0$ when $\varphi \le \varphi_{++}$, $B = 0$, $A = \eta_A(0,\varphi_{++})$, and $h < 0$ when $\varphi \ge \varphi_{--}$, $A = 0$, $B = \eta_B(0,\varphi_{--})$.

(PF) with (USV1)–(USV2) makes the zero sets $\{f_A = 0\}$ and $\{f_B = 0\}$ graphs with slopes below $-1$ (Lemma 4). Then, given $0 < a < b < 1$ and $\varphi_{--} < c < d < \varphi_{++}$, for $\epsilon_e,\epsilon_m$ small there is an orbit whose $(R,\varphi)$ coordinates avoid $[a,b]\times[c,d]$ and along which $R$ fluctuates between values above $b$ and below $a$.

## Expansion

By (PF) the divergence of the vector field is positive on any compact set of interior states once $\epsilon_m,\epsilon_e$ are small, so the flow is area-expanding there: no interior fixed point can be stable, and almost every orbit leaves any compact interior set $K$. Outside the central rectangle the dynamics are a relaxation oscillation. When $R$ is near $1$, $\varphi$ slowly increases; once $\varphi$ passes $\varphi_{++}$ the fast ecology sends $R$ near $0$ while $\varphi$ barely moves; then $\varphi$ slowly decreases until it falls below $\varphi_{--}$, and $R$ jumps back near $1$. Mutation keeps both phenotypes present at order $\epsilon_m$, so the switches never stall at the boundary. Without mutation one phenotype goes extinct; with fast feedback or fast mutation the system reaches an equilibrium (stasis).

In the variable-size model, for intermediate $\varphi$ the $(A,B)$ phase plane has a repelling origin, a saddle and two attractors near the axes; the slow drift of $\varphi$ destroys one attractor at a time, producing the same alternation.

## Sources

- Meike T. Wortel, Han Peters, Juan A. Bonachela, Nils Chr. Stenseth, "Continual evolution through coupled fast and slow feedbacks", Proceedings of the National Academy of Sciences 117 (2020), 4234–4242, <https://doi.org/10.1073/pnas.1916345117>. Published version of arXiv:1901.01885, cited next; locators there refer to the arXiv version.
- Meike T. Wortel, Han Peters, Nils Chr. Stenseth, "Coupled fast and slow feedbacks lead to continual evolution: A general modeling approach," arXiv 2019. Supplementary information: Lemma 1, Lemma 2, Theorem 3 (constant population size), Lemma 4 and Theorem 5 (variable population size). <https://doi.org/10.48550/arXiv.1901.01885>
