# Conserved combinations in multispecies transport on a box

On a nondegenerate closed rectangular box $\Omega=\prod_{i=1}^3[a_i,b_i]$ with $a_i<b_i$, and an open time interval $I$,
let finitely many species concentrations $c$ and fluxes $J$ be continuously differentiable on a neighbourhood of $I\times\Omega$ and satisfy $c_t + \nabla \cdot J = S\,r(c)$ with stoichiometric matrix $S$
and continuous rates $r$. If $\ell^{\mathsf T} S = 0$, then

$$\frac{d}{dt}\int_\Omega \ell^{\mathsf T} c\,dV = -\oint_{\partial\Omega} \ell^{\mathsf T} J \cdot n\,dA,$$

with outward normal $n$, by differentiating under the integral and the divergence theorem on the box; with no flux through the boundary
for all times in $I$, the total $\int_\Omega \ell^{\mathsf T} c$ is constant on $I$. The identity holds for any real left-null vector $\ell$.
With molar concentrations, element-count rows of a balanced stoichiometric matrix give the particular interpretation as conserved
element amounts; an arbitrary left-null row need not be an element-count row. Other domains are not covered.

## Depends on

## Proof depends on

## Sources

- OpenStax, *Calculus Volume 3*, Section 6.8, the divergence theorem (Theorem 6.20), <https://openstax.org/books/calculus-volume-3/pages/6-8-the-divergence-theorem>.
- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Exercise 2.8, Equation 2.67, the element balance of a balanced stoichiometric matrix (pp. 58–59).
