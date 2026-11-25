# Finite-order differentiation of heat evolution

Let $P_t$ denote whole-line Gaussian heat evolution, extended by $P_tg=g$
for $t\le0$, and let

$$
D_\nu f(t,x)=\int_0^t P_{\nu(t-s)}(f(s,\cdot))(x)\,ds.
$$

Write $J_k f(s,x)=\partial_x^k f(s,x)$ for the actual iterated ordinary
spatial derivative, with $J_0f=f$.

Let $n\in\mathbb N$ and $g\in C^n(\mathbb R)$. Suppose every actual derivative
$g^{(k)}$, $0\le k\le n$, has exponential growth: for each such $k$ there are
$M_k,c_k\ge0$ with $|g^{(k)}(x)|\le M_k e^{c_k|x|}$ for all real $x$.
Then, for every $t,x\in\mathbb R$,

$$
\partial_x^n(P_tg)(x)=P_t(g^{(n)})(x).
$$

The identity includes the stationary extension at $t\le0$ and order $n=0$.
Its proof iterates the first-derivative transfer identity, using actual
iterated derivatives rather than independently supplied derivative fields.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §§2.3–2.4: Gaussian differentiation and Duhamel formula (4.42). The finite-order weighted statements here are derived by iterating the proved derivative-transfer formulas and applying the continuous-forcing Gaussian gradient estimates; the source is background for the classical formulas, not a statement of these precise exponential-growth hypotheses.
