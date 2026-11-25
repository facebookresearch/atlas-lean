# Continuity of transferred Duhamel derivatives

Let $P_t$ denote whole-line Gaussian heat evolution, extended by $P_tg=g$
for $t\le0$, and let

$$
D_\nu f(t,x)=\int_0^t P_{\nu(t-s)}(f(s,\cdot))(x)\,ds.
$$

Write $J_k f(s,x)=\partial_x^k f(s,x)$ for the actual iterated ordinary
spatial derivative, with $J_0f=f$.
Let $n\in\mathbb N$. For each $s\in[0,T]$, assume $f(s,\cdot)\in C^n(\mathbb R)$.
For every $0\le k\le n$, assume $J_kf$ is jointly continuous on
$[0,T]\times\mathbb R$ and there are constants $M_k,c_k\ge0$ such that

$$
|J_k f(s,x)|\le M_k e^{c_k|x|}
\qquad(0\le s\le T,\ x\in\mathbb R).
$$

The constants may depend on the derivative order. No time derivative of the
forcing is assumed.

If $\nu\ge0$ and $T\ge0$, the actual derivative field
$(t,x)\mapsto\partial_x^nD_\nu f(t,x)$ is jointly continuous on
$[0,T]\times\mathbb R$.

Transfer identifies it with the Duhamel integral of the continuous,
uniformly exponentially growing field $J_nf$. The closed strip includes
both endpoints and the degenerate horizon $T=0$.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §§2.3–2.4: Gaussian differentiation and Duhamel formula (4.42). The finite-order weighted statements here are derived by iterating the proved derivative-transfer formulas and applying the continuous-forcing Gaussian gradient estimates; the source is background for the classical formulas, not a statement of these precise exponential-growth hypotheses.
