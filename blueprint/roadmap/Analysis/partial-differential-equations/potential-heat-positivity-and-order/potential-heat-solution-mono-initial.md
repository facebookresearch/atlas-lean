# Order preservation for actual potential-heat evolution

Let $\nu>0$ and $T\in\mathbb R$. For every $s\in[0,T]$, the spatial potential
slice $q(s,\cdot)$ is $C^2$. For $j=0,1,2$, the actual derivative
$\partial_x^j q$ is jointly continuous on $[0,T]\times\mathbb R$ and has a
uniform finite absolute bound there; these bounds may depend on $j$. No potential
time derivative is required.

Write $P_{\nu t}g$ for the free Gaussian heat evolution and
$\Phi_{\nu,q,g}$ for the actual Volterra solution. Every initial datum considered
is continuous and has exponential growth: $|g(x)|\le A e^{c|x|}$ for some
$A,c\ge0$. No initial spatial derivative is required.

Let $f,g$ be two initial data satisfying the continuity and exponential-growth
hypotheses above, with separate growth constants permitted. If $f(x)\le g(x)$
for every $x$, then

$$
\Phi_{\nu,q,f}(t,x)\le\Phi_{\nu,q,g}(t,x)
\qquad(0\le t\le T,\ x\in\mathbb R).
$$

Neither datum needs to be nonnegative or bounded. Both constructions have zero
potential-heat residual and have their own uniform exponential strip bounds.
Their ordered initial values therefore give the result by residual comparison,
including the terminal endpoint by continuity.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §2.8, gives the zeroth-order maximum-principle background. The stated weighted whole-line estimates follow by comparing the constructed solution with exponential time multiples of free heat; the reference is not asserted to state these exact growth and endpoint hypotheses.
