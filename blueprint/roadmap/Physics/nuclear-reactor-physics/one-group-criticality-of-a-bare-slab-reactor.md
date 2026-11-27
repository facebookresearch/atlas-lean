# One-group criticality of a bare slab reactor

Consider a homogeneous slab reactor occupying $-a/2 \le x \le a/2$, infinite in the other two directions, described by steady one-group neutron diffusion with the following data:
- diffusion coefficient $D > 0$;
- macroscopic absorption cross-section $\Sigma_a > 0$;
- infinite-medium multiplication factor $k_\infty > 0$.

Write $L^2 = D/\Sigma_a$ for the diffusion area. The neutron flux $\phi$ satisfies

$$
D\,\phi''(x) - \Sigma_a\,\phi(x) + k_\infty \Sigma_a\,\phi(x) = 0, \qquad \phi(\pm a/2) = 0,
$$

where the zero-flux boundary condition is imposed at the faces and the extrapolation distance is neglected.

**Theorem.** A nonnegative flux that is not identically zero exists if and only if

$$
k_\infty = 1 + L^2 B^2, \qquad B = \frac{\pi}{a}.
$$

That is, the material buckling $(k_\infty - 1)/L^2$ equals the geometric buckling $(\pi/a)^2$. In that case the flux is $\phi(x) = A\cos(\pi x/a)$ for some $A > 0$, and its amplitude, hence the power level, is not determined by the equation.

**Proof.** The equation reads $\phi'' + \bigl((k_\infty - 1)/L^2\bigr)\phi = 0$.
- If $k_\infty \le 1$, every solution is a combination of $\cosh$ and $\sinh$, or is affine, and vanishing at both faces forces $\phi \equiv 0$.
- If $k_\infty > 1$, set $B_m^2 = (k_\infty - 1)/L^2$, so that $\phi = A\cos(B_m x) + C\sin(B_m x)$. A nonzero solution meeting both boundary conditions requires $B_m a = n\pi$ for some integer $n \ge 1$. For $n \ge 2$, every such solution changes sign on the slab. For $n = 1$, $\sin(B_m x)$ does not vanish at the faces, so $C = 0$, and $\phi = A\cos(\pi x/a)$ is nonnegative exactly when $A \ge 0$.

The criticality condition is an eigenvalue identity for an idealized model. It does not establish reactor operating limits, boiling or critical-heat-flux margins, or safety. Those require transport, thermal-hydraulic and empirical qualification models.

## Sources

- M. Ragheb, *One Group Reactor Theory*, lecture notes for NPRE 402 / ME 405 Nuclear Power Engineering, University of Illinois, 2019, <https://mragheb.com/NPRE%20402%20ME%20405%20Nuclear%20Power%20Engineering/One%20Group%20Reactor%20Theory.pdf>:
    - Section 4: one-group diffusion with fission source, the diffusion area $L^2 = D/\Sigma_a$, and material versus geometric buckling;
    - Section 5: the criticality equation $B_g^2 = B_m^2$ and $k_{\mathrm{eff}} = k_\infty P_f/(1 + L^2B^2)$;
    - Section 7: the bare slab of thickness $a$, with $\phi = A\cos(Bx)$, $Ba = n\pi$, the fundamental mode $B = \pi/a$, and the extrapolation length neglected. Here the fast non-leakage probability is $P_f = 1$, as in the pure one-group model.
