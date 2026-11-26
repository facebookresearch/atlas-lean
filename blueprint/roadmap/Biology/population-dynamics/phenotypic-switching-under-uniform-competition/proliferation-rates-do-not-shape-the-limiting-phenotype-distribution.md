# Proliferation rates do not shape the limiting phenotype distribution

**Model.** Cells carry a continuous phenotype $x\in\Omega$ and switch phenotype by advection–diffusion; proliferation depends on phenotype but is braked by a factor common to all phenotypes that depends only on the total population:

$$\partial_tu=\mathcal Lu+g\bigl(U(t)\bigr)\,r(x,t)\,u,\qquad \mathcal Lu=-\partial_x\bigl(v(x)u\bigr)+\partial_x\bigl(D(x)\partial_xu\bigr),\qquad U(t)=\int_\Omega u\,dx,$$

with no-flux boundary conditions. Here $g$ is decreasing with a single zero at the carrying capacity $U^*$ (e.g. logistic $1-U/K$ or Gompertz $\ln(K/U)$), $0\le r\le r_{\max}$, and $\psi$ is the stationary probability density of the switching dynamics $\partial_tu=\mathcal Lu$.

**Theorem (bounded phenotype space).** Let $\Omega=[0,\ell]$ under the paper's regularity and positivity hypotheses (H1)–(H4), and $u_0\ge0$ in $L^1$ with $U_0>0$. Then:
1. there is a unique global nonnegative mild solution;
2. $U(t)$ is monotone and $U(t)\to U^*$;
3. there are $C\ge1$ and $\lambda>0$, depending only on $\ell$, $D$ and $v$, such that

$$\|u(t)-U(t)\psi\|_{L^1}\le Ce^{-\lambda t}\|u_0-U_0\psi\|_{L^1}+2C\int_0^te^{-\lambda(t-s)}|U'(s)|\,ds\to0 .$$

Hence $u(t)\to U^*\psi$ in $L^1$, whatever the proliferation rates $r(x,t)$.

**Whole line.** On $\Omega=\mathbb R$, if $r\ge r_{\min}>0$ on a fixed bounded interval for large $t$ and the switching dynamics has a stationary density $\psi$, then again $U(t)\to U^*$ monotonically and $u(t)\to U^*\psi$ in $L^1(\mathbb R)$; moreover the nonlinear solution is asymptotically equal to the linear switching semigroup applied to any datum of mass $U^*$.

## Expansion

Because the brake $g(U)$ is common to all phenotypes, the total population solves the scalar equation $U'=g(U)\int r\,u\,dx$, whose sign is that of $g(U)$, so $U$ converges monotonically to $U^*$ and the net proliferation term $g(U)r$ vanishes asymptotically. Then $u$ follows the linear switching semigroup, a Markov semigroup that contracts $L^1$ towards $\psi$ exponentially on a bounded interval (spectral gap $\lambda_1$); Duhamel's formula gives the inequality in item 3. Fitness differences affect transients but not the limit.

## Sources

- Artur César Fassoni, "Fitness is asymptotically irrelevant under uniform competition in phenotype-structured populations", arXiv:2609.32585 (2026), Section 2, Theorems 1 and 2, Section 4, <https://doi.org/10.48550/arXiv.2609.32585>.
