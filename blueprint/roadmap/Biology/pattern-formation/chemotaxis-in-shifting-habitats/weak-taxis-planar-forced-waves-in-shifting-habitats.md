# Weak-taxis planar forced waves of chemotaxis in shifting habitats

**Setting.** In the shifting-habitat Keller–Segel model

$$u_t=a_0\Delta u-\eta\chi(t)\nabla\cdot(u\nabla v)+u\,f(t,x\cdot e-ct,u),\qquad \tau v_t=d(t)\Delta v-\nu(t)v+\mu(t)u,$$

with constant population diffusivity $a_0>0$, $T$-periodic coefficients and KPP-type $f$, a **planar forced wave** is a solution $(u,v)=(U(t,\xi),V(t,\xi))$, $\xi=x\cdot e-ct$, that is $T$-periodic in $t$, tends to the positive periodic favorable state as $\xi\to-\infty$ and to $0$ as $\xi\to+\infty$. Let $c_*=2\sqrt{a_0\bar r}$ and let $U_c$ be the zero-taxis ($\eta=0$) scalar forced wave at speed $c$.

**Theorem.** Fix $\tau\ge0$ and a compact interval $I\Subset(-\infty,c_*)$. Assume the nondegenerate pinning condition $-U_c\,f_\xi(t,\xi,U_c)\not\equiv0$ on $[0,T]\times\mathbb R$ for every $c\in I$, and joint $C^1$ regularity of $f$. Then there are $\eta_{I,\tau}>0$ and a two-sided exponential weight such that for all $c\in I$ and $0\le\eta\le\eta_{I,\tau}$ the system has a planar forced $T$-periodic wave $(U_{\eta,\tau,c},V_{\eta,\tau,c})$, locally unique among solutions with the same end states in the weighted space. Moreover, uniformly in $c\in I$,

$$\begin{pmatrix}U_{\eta,\tau,c}\\ V_{\eta,\tau,c}\end{pmatrix}=\begin{pmatrix}U_c\\ V_{\tau,c}\end{pmatrix}+\eta\begin{pmatrix}H_{\tau,c}\\ K_{\tau,c}\end{pmatrix}+O(\eta^2),$$

where $(H_{\tau,c},K_{\tau,c})$ is the unique periodic weighted solution of $\mathcal A_cH=-\chi(t)\big(U_c(V_{\tau,c})_\xi\big)_\xi$, $\mathcal B_{\tau,c}K=\mu(t)H$.

## Depends on

- [Spreading of Keller–Segel populations in a shifting time-periodic habitat](spreading-of-keller-segel-populations-in-a-shifting-periodic-habitat.md)

## Expansion

Because the habitat edge breaks translation invariance, the scalar forced wave $U_c$ is pinned to the climate front and its linearization $\mathcal A_c$ has no translational kernel; the pinning condition makes $\mathcal A_c$ invertible between two-sided exponentially weighted periodic spaces (Fredholm of index zero with trivial kernel). The full system is triangular at $\eta=0$, so the implicit function theorem in $\eta$ yields a locally unique branch, and differentiating at $\eta=0$ gives the first-order chemotactic response $(H,K)$ with a uniform quadratic remainder.

## Sources

- Hoang-Hung Vo, "Time-Periodic Chemotaxis in Shifting Environments: Propagation and Planar Forced Waves in $\mathbb R^N$", arXiv:2610.36627 (2026), Theorems 1.4 and 1.5, <https://doi.org/10.48550/arXiv.2610.36627>.
