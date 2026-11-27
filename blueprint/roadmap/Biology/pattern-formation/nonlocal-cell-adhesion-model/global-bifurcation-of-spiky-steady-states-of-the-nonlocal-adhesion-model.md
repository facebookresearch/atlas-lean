# Global bifurcation of spiky steady states of the nonlocal adhesion model

**Model.** On the circle $S^1_L$ of length $L>2$ (sensing radius normalized to $1$, diffusion to $1$), the Armstrong–Painter–Sherratt nonlocal adhesion model for a cell density $u(x,t)$ is

$$u_t = u_{xx} - \alpha\,\big(u\,\mathcal K[u]\big)_x, \qquad \mathcal K[u]\,(x) = \int_{-1}^{1} h\big(u(x+r)\big)\,\Omega(r)\,dr,$$

with adhesion strength $\alpha$, adhesive force function $h$, and an odd kernel $\Omega(r) = \operatorname{sign}(r)\,\omega(r)$, where $\omega \ge 0$ is even, $\omega \in L^1 \cap L^\infty(0,1)$, $\|\omega\|_{L^1(0,1)} = \tfrac12$, and

$$M_n(\omega) = \int_0^1 \sin\!\Big(\frac{2\pi n r}{L}\Big)\,\omega(r)\,dr > 0$$

for infinitely many $n$. Steady states solve $u'' = \alpha\,(u\,\mathcal K[u])'$ on $S^1_L$ with prescribed mean $\bar u > 0$; the constant $\bar u$ is a solution for every $\alpha$.

**Local bifurcation.** For each $n$ with $M_n(\omega)>0$, the constant state bifurcates at

$$\alpha_n = \frac{n\pi}{\bar u\, h'(\bar u)\, L\, M_n(\omega)}, \qquad e_n(x) = \cos\!\Big(\frac{2\pi n x}{L}\Big),$$

and near $(\alpha_n,\bar u)$ all nontrivial steady states lie on a curve $u_n(x,s) = \bar u + s\,\alpha_n e_n(x) + o(s)$ (Crandall–Rabinowitz).

**Theorem (global bifurcation, linear adhesion $h(u)=u$, uniform kernel $\omega\equiv\tfrac12$).** Restrict to the space $H^2_{\Sigma_n}$ of $L/n$-periodic, even functions (dihedral symmetry $\Sigma_n$). The steady-state set contains a closed connected continuum $\mathcal C \subset \mathbb R \times H^2_{\Sigma_n}$ such that

1. $\mathcal C$ contains the local branch through $(\alpha_n,\bar u)$;
2. every $(\alpha,u) \in \mathcal C$ has $\alpha > 0$ and $u > 0$;
3. $\mathcal C = \mathcal C^+ \cup \mathcal C^-$ with $\mathcal C^+ \cap \mathcal C^- = \{(\alpha_n,\bar u)\}$, and away from the bifurcation point the two unilateral branches consist of *$n$-spiky* functions: $u'$ has exactly $2n$ simple zeros, located at the tile boundaries $x = mL/(2n)$, with alternating sign of $u'$ on consecutive tiles;
4. both unilateral branches are unbounded: for every $\alpha \ge \alpha_n$ each of $\mathcal C^\pm$ contains a solution with that $\alpha$.

Consequently, for $h(u)=u$, $\omega\equiv\tfrac12$ and every $\alpha > \alpha_n$, the periodic steady-state problem has at least two distinct $n$-spiked solutions, one peaked at $x=0$ and one at $x = L/(2n)$.

## Expansion

The proof combines the Rabinowitz–López-Gómez unilateral global bifurcation alternative with equivariance. Restricting to $H^2_{\Sigma_n}$ makes the $n$-th eigenvalue simple. The nodal structure (spiky property) is an open and closed condition along the branch: symmetry forces $u' = 0$ and $\mathcal K[u] = 0$ at the tile boundaries, and the identity $\mathcal K[u] = \Delta_1 w$ for the modified area function $w(x) = \int_0^x u - \bar u x$ (for the uniform kernel) shows $\mathcal K[u]$ cannot vanish inside a tile. Hence a branch cannot return to the trivial line at another $\alpha_{kn}$ or connect $\mathcal C^+$ to $\mathcal C^-$, so the alternative of the unilateral theorem forces unboundedness; a priori bounds for fixed $\alpha$ make it unbounded in $\alpha$.

## Sources

- Andreas Buttenschön and Thomas Hillen, "Non-Local Cell Adhesion Models: Steady States and Bifurcations", arXiv:2001.00286 (2020); chapter "Local Bifurcation" (local bifurcation theorem and the eigenvalue formula for $\alpha_n$) and chapter "Global Bifurcation" (global bifurcation theorem, spiky function spaces, and the theorem on at least two $n$-spiked solutions), <https://doi.org/10.48550/arXiv.2001.00286>.
