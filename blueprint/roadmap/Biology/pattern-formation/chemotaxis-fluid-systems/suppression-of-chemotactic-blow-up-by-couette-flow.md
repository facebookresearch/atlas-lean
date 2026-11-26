# Suppression of chemotactic blow-up by a strong Couette flow in generalized Hillen–Painter models

**Model.** On $\mathbb R^2$, a cell density $n$ with signal $c$ is advected by a Navier–Stokes perturbation $u$ of the Couette flow $(Ay,0)$ of amplitude $A$, with buoyancy forcing:
$$\begin{cases}
\partial_tn+Ay\,\partial_xn+u\cdot\nabla n-\Delta n=-\nabla\cdot\big[n(\kappa n+\mu)\nabla c\big],\\
-\Delta c=n-\alpha c,\\
\partial_tu+Ay\,\partial_xu+\binom{Au_2}{0}+u\cdot\nabla u-\Delta u+\nabla p=\binom0n,\qquad\nabla\cdot u=0.
\end{cases}$$
The sensitivity $n(\kappa n+\mu)$ generalizes the Hillen–Painter volume-filling model; $\kappa>0$ is the *supercritical* case, in which solutions without flow can blow up in finite time for any initial mass $M=\|n_{\rm in}\|_{L^1}$. Let $\omega=\operatorname{curl}u$.

**Theorem.** Let $0<\epsilon<\tfrac12<m$, with $\epsilon>\tfrac13$ if $\alpha=0$. Let $u_{\rm in}\in H^2(\mathbb R^2)$ and $0\le n_{\rm in}\in L^1\cap L^\infty$, and assume $\|\omega_{\rm in}\|_{Y_{m,\epsilon}}+\|\langle D_x\rangle^{1/3}n_{\rm in}\|_{Y_{m,\epsilon}}<\infty$, where $Y_{m,\epsilon}$ weights $x$-frequencies by $\langle D_x\rangle^m\langle D_x^{-1}\rangle^\epsilon$. There is $C^*=C^*(\epsilon,m,\kappa,\mu,\alpha)$ such that if
$$A>C^*\Big(\|n_{\rm in}\|_{L^\infty}^2\chi_{|\kappa|+|\mu|>0}+M^2\chi_{|\mu|>0}+\|\omega_{\rm in}\|_{Y_{m,\epsilon}}^2+\|\langle D_x\rangle^{1/3}n_{\rm in}\|_{Y_{m,\epsilon}}^2+1\Big)^{3+12\chi_{|\kappa|>0}+6\chi_{|\mu|>0}-3\chi_{|\kappa||\mu|>0}},$$
then the solution is global and smooth, and for all $t\ge0$
$$\|n\|_{L^\infty_{t,x}}\le C\big(\|n_{\rm in}\|_{L^\infty}^6+M^6+\|\omega_{\rm in}\|_{Y_{m,\epsilon}}^6+\|\langle D_x\rangle^{1/3}n_{\rm in}\|_{Y_{m,\epsilon}}^6+1\big).$$
In particular, no mass threshold is needed: a sufficiently strong shear prevents blow-up for every initial mass.

## Expansion

After rescaling time by $A^{-1}$, the equations become transport by $y\partial_x$ with diffusion $\frac1A\Delta$ and a nonlinearity of size $\frac1A$. Shear combined with diffusion damps the $x$-dependent modes on the enhanced-dissipation time scale $A^{1/3}|k|^{-2/3}$, much faster than diffusion alone. The norms $X_a$ carry the weight $e^{2aA^{-1/3}|D_x|^{2/3}t}$ to capture this. The $x$-averaged part ($k=0$) is not mixed. Earlier work on $\mathbb T\times\mathbb R$ needed a mass threshold to control it, because it behaves like a one-dimensional chemotaxis problem. Here a frequency decomposition separates very low $x$-frequencies, which are weighted by $\langle D_x^{-1}\rangle^\epsilon$, from the rest on the whole plane, and a bootstrap closes the energy estimates once $A$ exceeds the stated polynomial in the data.

## Sources

- Yubo Chen, Wendong Wang, Guoxu Yang, Yi Zhang, "Global bounded solutions for a class of generalized Hillen-Painter models near Couette flow in $\mathbb{R}^2$", arXiv:2606.18592 (2026), Section 1 (system and rescaled form), Theorem 1.1, Propositions 2.2 and 2.6, <https://doi.org/10.48550/arXiv.2606.18592>.
