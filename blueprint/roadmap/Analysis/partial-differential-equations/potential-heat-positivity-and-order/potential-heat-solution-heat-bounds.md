# Quantitative free-heat bounds for potential evolution

Let $\nu>0$ and $T\in\mathbb R$. For every $s\in[0,T]$, the spatial potential
slice $q(s,\cdot)$ is $C^2$. For $j=0,1,2$, the actual derivative
$\partial_x^j q$ is jointly continuous on $[0,T]\times\mathbb R$ and has a
uniform finite absolute bound there; these bounds may depend on $j$. No potential
time derivative is required.

Write $P_{\nu t}g$ for the free Gaussian heat evolution and
$\Phi_{\nu,q,g}$ for the actual Volterra solution. Every initial datum considered
is continuous and has exponential growth: $|g(x)|\le A e^{c|x|}$ for some
$A,c\ge0$. No initial spatial derivative is required.

Suppose $g\ge0$ and a supplied constant $Q\ge0$ satisfies $|q(s,x)|\le Q$
throughout the closed strip. Then, for every $0\le t\le T$ and every $x$,

$$
e^{-Qt}P_{\nu t}g(x)\le\Phi_{\nu,q,g}(t,x)\le e^{Qt}P_{\nu t}g(x).
$$

The parameter $Q$ in the displayed estimate is explicit and may be chosen
separately from the derivative bounds. Both endpoints are included. Free heat
preserves the nonnegativity of $g$. Its multiples $e^{-Qt}P_{\nu t}g$ and
$e^{Qt}P_{\nu t}g$ have potential-heat residuals of the appropriate signs,
namely $(-Q-q)e^{-Qt}P_{\nu t}g$ and $(Q-q)e^{Qt}P_{\nu t}g$.
Their continuity, actual derivatives and uniform exponential strip growth justify
comparison with $\Phi$. Positivity of $\Phi$ is not assumed in this argument.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §2.8, gives the zeroth-order maximum-principle background. The stated weighted whole-line estimates follow by comparing the constructed solution with exponential time multiples of free heat; the reference is not asserted to state these exact growth and endpoint hypotheses.
