# Uniform vaccination is optimal or worst for constant-degree kernels

**Setting.** Let $(\Omega,\mu)$ be a probability space of individual types and $\mathrm{k}\ge0$ a next generation kernel with finite $L^2$ double norm and spectral radius $R_0>0$. A strategy $\eta:\Omega\to[0,1]$ is the unvaccinated fraction, with cost $C(\eta)=1-\int\eta\,d\mu$ and effective reproduction number $R_e(\eta)=\rho(T_{\mathrm{k}\eta})$, as in [Pareto frontier of vaccination strategies in the kernel SIS model](../pareto-optimal-vaccination-in-heterogeneous-sis-models/pareto-frontier-of-vaccination-strategies-in-the-kernel-sis-model.md). The kernel has *constant degree* if $x\mapsto\mathrm{k}(x,\Omega)$ and $y\mapsto\mathrm{k}(\Omega,y)$ are constant (all in- and out-degrees equal); then $\mathbf{1}$ is a left and right Perron eigenfunction with eigenvalue $R_0$. The uniform strategies are $\eta\equiv1-c$, with $R_e=(1-c)R_0$. Examples: adjacency kernels of regular graphs (with $R_0=d$) and of regular directed graphs.

**Theorem.** Let $\mathrm{k}$ have constant degree.

1. If $R_e$ is convex on the strategy set, every uniform strategy is Pareto optimal: the minimal $R_e$ at cost $c$ is $(1-c)R_0$ and stopping transmission completely ($R_e=0$) requires vaccinating everyone (the minimal cost $c_\star=\inf\{c:R_e^\star(c)=0\}$ is $1$).
2. If $R_e$ is concave, $\mathrm{k}$ is irreducible and every uniform strategy is anti-Pareto optimal: the worst $R_e$ at cost $c$ is $(1-c)R_0$, and every non-trivial strategy does some good.
3. For a symmetric constant-degree kernel, convexity holds when $T_\mathrm{k}$ is positive semi-definite, and concavity holds when $R_0$ is a simple eigenvalue and $T_\mathrm{k}$ is negative semi-definite on the orthogonal complement of $\mathbf{1}$ (all other eigenvalues non-positive).

For example, in the fully asymmetric circle (each of $N$ equal groups infects only the next), $R_e$ is far from convex: giving all vaccine to one group is optimal, stopping transmission completely ($R_e=0$) costs only $1/N$, the best reproduction number at cost $c$ is $(1-Nc)_+^{1/N}$ (with $R_0=1$), and the uniform strategies are the worst.

## Expansion

Since $\mathbf{1}$ is a Perron eigenfunction on both sides, $R_e$ is differentiable at $\mathbf{1}$ with derivative proportional to $\int(\eta-1)\,d\mu$, so to first order $R_e$ depends only on the cost. The uniform segment from $(0,R_0)$ to $(1,0)$ is the chord of the frontier; convexity of $R_e$ puts every strategy above its tangent at the uniform ray, so the uniform strategies are best, and concavity puts every strategy below it, so they are worst. In the symmetric case the sign of the spectrum gives convexity or concavity through the variational characterization of the spectral radius.

## Depends on

- [Pareto frontier of vaccination strategies in the kernel SIS model](../pareto-optimal-vaccination-in-heterogeneous-sis-models/pareto-frontier-of-vaccination-strategies-in-the-kernel-sis-model.md)

## Sources

- Jean-François Delmas, Dylan Dronnier, Pierre-André Zitt, "Optimal vaccination: Various (counter) intuitive examples", arXiv:2112.08756 (2021): Section 2 (uniform vaccination example; fully asymmetric circle proposition), Section 5 (definition of constant-degree kernels, examples, proposition on uniform strategies, corollary for symmetric kernels and the equivalent semi-definiteness conditions). <https://doi.org/10.48550/arXiv.2112.08756> Published version: Journal of Mathematical Biology 86 (2023) 26, <https://doi.org/10.1007/s00285-022-01858-5>.
