# Square-root rescaling of the Duhamel integral

Suppose $f$ is jointly continuous on $[0,T]\times\mathbb R$ with a uniform
exponential spatial bound. For $0\le t\le T$, arbitrary real $\nu$, and $x\in\mathbb R$,
$$
D_\nu f(t,x)=2t\int_0^1 r\,P_{\nu t r^2}(f(t(1-r^2),\cdot))(x)\,dr.
$$
The proof uses the differentiable substitution $s=t(1-r^2)$ and the continuity
of heat families. Nonpositive heat times use the existing stationary extension;
this algebraic identity makes no backward-heat or zero-viscosity smoothing claim.
At $t=0$ both sides vanish.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §2.3, pp. 16–17 (Gaussian differentiation), and §2.4, formula (4.42) (Duhamel construction). The explicit exponential-weight estimates and the continuous-forcing first-derivative conclusion are justified in the linked Lean proofs; the classical PDE theorem in the notes has stronger forcing regularity.
