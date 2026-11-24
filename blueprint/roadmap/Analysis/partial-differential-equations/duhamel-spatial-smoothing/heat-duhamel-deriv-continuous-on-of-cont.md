# Closed-strip continuity of the smoothed derivative

Let $\nu>0$ and let $f:[0,T]\times\mathbb R\to\mathbb R$ be jointly continuous,
with constants $M,c\ge0$ satisfying $|f(s,x)|\le M e^{c|x|}$ uniformly on the strip.
Write $D_\nu f(t,x)=\int_0^t P_{\nu(t-s)}(f(s,\cdot))(x)\,ds$.
No spatial or time derivative of $f$ is assumed.

Assume $T\ge0$. The map $(t,x)\mapsto\partial_xD_\nu f(t,x)$ is jointly continuous
on $[0,T]\times\mathbb R$, including its zero value at $t=0$.
The proof applies dominated convergence to the rescaled Gaussian first moment,
then continuity of integration on the fixed unit time interval. Clamping only
the forcing's time parameter avoids requiring continuity outside its strip.
The factor $\sqrt t$ is continuous at zero. This is spatial derivative continuity,
not a claim of time differentiability at either endpoint.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §2.3, pp. 16–17 (Gaussian differentiation), and §2.4, formula (4.42) (Duhamel construction). The explicit exponential-weight estimates and the continuous-forcing first-derivative conclusion are justified in the linked Lean proofs; the classical PDE theorem in the notes has stronger forcing regularity.
