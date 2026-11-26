# Uniform boundedness of radial subcritical Keller–Segel solutions on the plane

**Model.** The parabolic–parabolic Keller–Segel system on $\mathbb R^2$,
$$\partial_tu=\Delta u-\nabla\cdot(u\nabla v),\qquad \tau\partial_tv=\Delta v-\lambda v+u,\qquad \tau,\lambda>0,$$
with nonnegative data $(u_0,v_0)\in L^1(\mathbb R^2)\times H^1(\mathbb R^2)$. For total mass $\|u_0\|_1<8\pi$ global existence is known, while finite-time blow-up can occur above $8\pi$.

**Theorem.** Let $(u_0,v_0)$ be radially symmetric with $\|u_0\|_{L^1}<8\pi$. Then the radial nonnegative global solution is bounded uniformly in time: for every $t_0>0$,
$$\sup_{t\ge t_0}\bigl(\|u(t)\|_{L^\infty}+\|\nabla v(t)\|_{L^\infty}\bigr)<\infty .$$

## Expansion

On bounded domains the Nagai–Senba–Yoshida free-energy method gives boundedness under the optimal mass condition, but on the whole plane the free energy of self-similar-type solutions tends to $-\infty$, so the global functional cannot be used. The proof localizes: for a cutoff $\varphi_R$ the localized free energy $\mathcal F_R$ and its dissipation
$$\mathcal D_R=\int u\,|\nabla(\ln u-v)|^2\varphi_R^2+\tau\int|\partial_tv|^2\varphi_R^2$$
satisfy $\frac{d}{dt}\mathcal F_R+\alpha\mathcal F_R+\beta\mathcal D_R\le C(R)$, given exterior control that radial symmetry provides through uniform decay away from the origin. This yields a uniform bound on $\int u\ln u\,\varphi_R^2$ near the origin, the only place where concentration can occur, and parabolic regularity finishes the argument.

## Sources

- Tatsuya Hosono, "Boundedness of radial solutions to the parabolic-parabolic Keller–Segel system on the plane with subcritical mass", arXiv:2610.28230 (2026), Theorem 1.1, Propositions 3.1 and 3.7, <https://doi.org/10.48550/arXiv.2610.28230>.
