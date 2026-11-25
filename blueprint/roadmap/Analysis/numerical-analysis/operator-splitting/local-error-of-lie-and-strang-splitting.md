# Local error of Lie and Strang splitting

Fix an induced operator norm and let $A$ and $B$ be fixed real $d \times d$ matrices, for example the semi-discrete transport and the linear reaction operators of an
advection–diffusion–reaction system $u' = (A + B)u$. For a step $h$ the Lie and Strang splitting steps are $e^{hA}e^{hB}$ and
$e^{hA/2}e^{hB}e^{hA/2}$. There are $C, h_0 > 0$ such that for $\lvert h\rvert \le h_0$

$$\Bigl\lVert e^{hA}e^{hB} - e^{h(A+B)} - \tfrac{h^2}{2}(AB - BA) \Bigr\rVert \le C\lvert h\rvert^3,
\qquad \bigl\lVert e^{hA/2}e^{hB}e^{hA/2} - e^{h(A+B)} \bigr\rVert \le C\lvert h\rvert^3 .$$

So the local error of Lie splitting has leading term $\tfrac{h^2}{2}[A, B]$, whose coefficient vanishes exactly when $AB=BA$, and
Strang splitting has local error $O(h^3)$. For fixed $T>0$, positive steps $0<h\le h_0$ and integers $n\ge0$ with $nh\le T$, since $\lVert e^{hA}\rVert \le e^{\lvert h\rvert\lVert A\rVert}$ and
likewise for $B$, the global operator errors at the grid times in $[0,T]$ are $O(h)$ for Lie and $O(h^2)$ for Strang splitting, with constants depending on
$T$, $\lVert A\rVert$ and $\lVert B\rVert$. If $AB = BA$ both splittings are exact. For a reaction and a transport step that do not
commute, for instance a spatially varying linear reaction rate under advection, the leading local error term
$\tfrac{h^2}{2}(AB - BA)\,u$ is nonzero for nonzero $h$ and every state $u$ with $(AB-BA)u\ne0$. Commutation of the two exponentials at one isolated step
is not the same as $AB=BA$. This fixed-matrix estimate does not assert a bound uniform under spatial-mesh refinement,
or an error theorem for unbounded differential operators, nonlinear reactions or incompatible boundary domains. Those require
separate domain, regularity and stability hypotheses.

## Depends on

## Proof depends on

## Sources

- D. Lanser and J. G. Verwer, Analysis of operator splitting for advection–diffusion–reaction problems from air pollution modelling, *Journal of Computational and Applied Mathematics* 111 (1999) 201–216, Section 2: Strang splitting, Equation (3), and the Baker–Campbell–Hausdorff expansion, Equation (10), <https://ir.cwi.nl/pub/1206/1206D.pdf>.
