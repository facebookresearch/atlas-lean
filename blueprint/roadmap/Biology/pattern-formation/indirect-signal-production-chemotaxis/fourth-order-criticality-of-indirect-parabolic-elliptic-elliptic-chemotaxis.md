# Fourth-order criticality of indirect parabolic–elliptic–elliptic chemotaxis

**Model (PES).** On $\Omega=\mathbb{R}^N$, $\mathbb{T}^N$ or a bounded $C^2$ domain with no-flux conditions, with $\chi,\tau>0$,
$$\partial_t u=\Delta u-\chi\nabla\cdot(u\nabla c),\qquad 0=\Delta w-w+u,\qquad 0=\tau\Delta c-c+w .$$
Eliminating the signals gives $c=K_\tau u$ with the positive self-adjoint fourth-order smoothing operator $K_\tau=(I-\tau\Delta)^{-1}(I-\Delta)^{-1}$, and the PES equation is the gradient flow $\partial_t u=\nabla\cdot\bigl(u\nabla(\log u-\chi K_\tau u)\bigr)$ of the free energy
$$\mathcal{F}_{\mathrm{PES}}[u]=\int_\Omega u\log u\,dx-\frac{\chi}{2}\int_\Omega u\,K_\tau u\,dx .$$
It arises from the two-stage signalling system when both signal relaxation times are short compared with cell migration.

**Results.**
1. *Energy dissipation.* Smooth positive solutions satisfy $\dfrac{d}{dt}\mathcal{F}_{\mathrm{PES}}[u]=-\displaystyle\int_\Omega u\,\bigl|\nabla(\log u-\chi K_\tau u)\bigr|^2dx\le0$.
2. *Scaling.* The scaling-critical Lebesgue exponent is $q_c=N/4$, so mass ($L^1$) is critical in dimension $N=4$, compared with $N=2$ for classical Keller–Segel.
3. *Variational instability.* For $N=4$ and mass $M>64\pi^2\tau/\chi$ there are densities $u_\varepsilon$ of mass $M$ with $u_\varepsilon\,dx\rightharpoonup M\delta_{x_0}$ and $\mathcal{F}_{\mathrm{PES}}[u_\varepsilon]\to-\infty$. This is a statement about the energy, not a proof of finite-time blow-up.
4. *Conditional global theory.* If a subcritical logarithmic bound on the interaction holds on the mass-$M$ class with constant $a<2/\chi$, then $\mathcal{F}_{\mathrm{PES}}\ge\delta\int u\log u-C$ with $\delta=1-\chi a/2>0$, which bounds the entropy and the dissipation on every $[0,T]$; loss of compactness at bounded energy can only occur by concentration of mass into Dirac masses.

## Expansion

The kernel of $K_\tau$ behaves like $-\frac{1}{8\pi^2\tau}\log|x-y|$ near the diagonal in $\mathbb{R}^4$, the Green's function of $\tau\Delta^2$, so the interaction energy of a concentrated bump of mass $M$ scales like $\frac{\chi M^2}{16\pi^2\tau}\log\frac1\varepsilon$, while the entropy grows like $4M\log\frac1\varepsilon$. The interaction wins when $M>64\pi^2\tau/\chi$, giving the variational instability. Below threshold the Adams inequality (the fourth-order analogue of Moser–Trudinger, with sharp constant $32\pi^2$ in dimension four) controls the exponential moment $\int e^{\chi K_\tau u}$, which via Gibbs duality bounds the interaction by the entropy. The dissipation identity is the standard computation for a Wasserstein gradient flow with a symmetric interaction kernel.

## Sources

- L. S. Wang, "Elliptic criticality versus Volterra memory in indirect chemotaxis cascades", arXiv:2606.12771 (2026), Proposition 1 (quasi-steady limit), Proposition 5, Proposition 7, Propositions 10–11, 13–14, Theorem 21 and Proposition 22, <https://doi.org/10.48550/arXiv.2606.12771>.
