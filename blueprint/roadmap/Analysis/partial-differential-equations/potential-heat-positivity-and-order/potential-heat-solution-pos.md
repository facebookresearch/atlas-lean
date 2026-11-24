# Strict positivity from pointwise positive data

Let $\nu>0$ and $T\in\mathbb R$. For every $s\in[0,T]$, the spatial potential
slice $q(s,\cdot)$ is $C^2$. For $j=0,1,2$, the actual derivative
$\partial_x^j q$ is jointly continuous on $[0,T]\times\mathbb R$ and has a
uniform finite absolute bound there; these bounds may depend on $j$. No potential
time derivative is required.

Write $P_{\nu t}g$ for the free Gaussian heat evolution and
$\Phi_{\nu,q,g}$ for the actual Volterra solution. Every initial datum considered
is continuous and has exponential growth: $|g(x)|\le A e^{c|x|}$ for some
$A,c\ge0$. No initial spatial derivative is required.

If $g(x)>0$ for every $x$, then
$\Phi_{\nu,q,g}(t,x)>0$ for all $0\le t\le T$ and all $x$.
There is no uniform positive lower bound assumption on $g$; in particular it
may tend to zero at spatial infinity or fail to be differentiable.

Free heat of these data is strictly positive, and multiplication by $e^{-Qt}$
preserves that sign. The quantitative lower bound therefore proves strict
positivity of the constructed field. Both initial and terminal times are
included, as is the degenerate horizon $T=0$. Negative horizons give an empty
set of claimed times.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §2.8, gives the zeroth-order maximum-principle background. The stated weighted whole-line estimates follow by comparing the constructed solution with exponential time multiples of free heat; the reference is not asserted to state these exact growth and endpoint hypotheses.
