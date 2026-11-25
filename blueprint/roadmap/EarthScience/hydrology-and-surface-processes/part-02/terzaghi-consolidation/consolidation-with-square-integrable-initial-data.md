# Consolidation with square-integrable initial data

For Terzaghi's equation $u_t=c_vu_{zz}$ with $c_v>0$ and drainage path $H_{\mathrm{dr}}>0$, distinguish the two boundary models.
With both faces drained, the full layer is $(0,2H_{\mathrm{dr}})$ with zero excess pore pressure at both endpoints; its sine modes are
$\sin(n\pi z/(2H_{\mathrm{dr}}))$, $n=1,2,\ldots$. With one face drained, the layer is $(0,H_{\mathrm{dr}})$ with
$u(t,0)=0$ and $u_z(t,H_{\mathrm{dr}})=0$; its modes are $\sin((n+\tfrac12)\pi z/H_{\mathrm{dr}})$, $n=0,1,\ldots$.

In each case every initial excess pore pressure in $L^2$ has a unique solution in the class continuous into $L^2$ up to $t=0$
and classical for $t>0$, given by its expansion in these modes with decay factors $e^{-c_v\lambda_n^2t}$, where $\lambda_n$ is the
corresponding spatial frequency. The solution is smooth for $t>0$ and converges to the initial data in $L^2$ as $t\to0^+$.
Reducing the double-drained layer to half its height with a zero-flux mid-plane requires initial data symmetric about the mid-plane;
it is not valid for arbitrary $L^2$ data. Uniform convergence of the series away from $t=0$ does not by itself establish the initial trace.

## Depends on

## Proof depends on

## Expansion

Link checked existence, uniqueness and initial-trace results with the stated boundary conditions and normalization. A homogeneous
Dirichlet theorem covers the full double-drained interval after scaling. For single drainage, use a checked mixed-boundary result or
prove the reflection reduction to a Dirichlet problem; do not silently substitute the Dirichlet theorem for a mixed-boundary theorem.

## Sources

- A. Verruijt, *Soil Mechanics*, Delft University of Technology, 2001, Chapter 15, consolidation: Terzaghi's equation, drainage conditions and the series solution, <http://geo.verruijt.net/>.
