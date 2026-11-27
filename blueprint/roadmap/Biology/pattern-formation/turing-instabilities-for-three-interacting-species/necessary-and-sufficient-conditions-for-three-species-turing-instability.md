# Necessary and sufficient conditions for three-species Turing instability

**Setting.** A reaction system $\dot{\mathbf n}=\mathbf f(\mathbf n)$ with $N=3$ species has a linearly stable steady state $\mathbf n^*$ with Jacobian $J=(J_{ij})$. In the reaction–diffusion system $\partial_tn_i=d_i\,\Delta n_i+f_i(\mathbf n)$, $d_i>0$, the Fourier mode with wavenumber $k$ evolves by $J(k^2)=J-k^2\,\mathrm{diag}(d_1,d_2,d_3)$. $\mathbf n^*$ admits a Turing–Hopf instability if some $J(k^2)$, $k^2>0$, has a complex-conjugate pair of eigenvalues with positive real part, and a Turing instability if it admits no Turing–Hopf instability and some $J(k^2)$ has a real positive eigenvalue.

**Cubic and quadratic tests.** Define

$$a_3=-(d_1+d_2)(d_2+d_3)(d_3+d_1),$$

$$a_2=(d_1+d_2)(d_1+d_2+2d_3)J_{33}+(d_2+d_3)(d_2+d_3+2d_1)J_{11}+(d_3+d_1)(d_3+d_1+2d_2)J_{22},$$

$$a_1=-\big[(d_1+d_2)M_{12}+(d_2+d_3)M_{23}+(d_3+d_1)M_{31}\big]-\mathrm{tr}J\,\big[d_1(J_{22}+J_{33})+d_2(J_{33}+J_{11})+d_3(J_{11}+J_{22})\big],$$

$$a_0=\mathrm{tr}J\ \mathrm{tr}(\mathrm{adj}\,J)-\det J,$$

with principal $2\times2$ minors $M_{ij}=J_{ii}J_{jj}-J_{ij}J_{ji}$, and

$$b_2=d_1d_2+d_1d_3+d_2d_3,\qquad b_1=-\big[d_1(J_{22}+J_{33})+d_2(J_{33}+J_{11})+d_3(J_{11}+J_{22})\big],\qquad b_0=\mathrm{tr}(\mathrm{adj}\,J).$$

For a cubic $g(y)=a_3y^3+a_2y^2+a_1y+a_0$ with $a_3<0$, $a_0<0$, condition (P1) is

$$a_2^2>3a_1a_3,\qquad a_2+\sqrt{a_2^2-3a_1a_3}>0,\qquad 2a_2^3+2(a_2^2-3a_1a_3)^{3/2}-9a_1a_2a_3+27a_0a_3^2>0,$$

which holds iff $g(y)>0$ for some $y>0$. For $h(y)=b_2y^2+b_1y+b_0$ with $b_2,b_0>0$, condition (P2) is

$$b_1<-2\sqrt{b_2b_0},\qquad 3a_3\big(b_1+\sqrt{b_1^2-4b_2b_0}\big)\le2b_0\big(a_2+\sqrt{a_2^2-3a_1a_3}\big)\le3a_3\big(b_1-\sqrt{b_1^2-4b_2b_0}\big),$$

$$g\Big(\tfrac{-b_1-\sqrt{b_1^2-4b_2b_0}}{2b_2}\Big)\le0,\qquad g\Big(\tfrac{-b_1+\sqrt{b_1^2-4b_2b_0}}{2b_2}\Big)\le0 .$$

Then $g(y)>0$ and $h(y)>0$ at a common $y>0$ iff (P1) holds and at least one inequality of (P2) fails.

**Theorem.** $\mathbf n^*$ admits a Turing–Hopf instability iff $(a_3,a_2,a_1,a_0)$ satisfy (P1) and $(b_2,b_1,b_0)$ violate at least one inequality of (P2). It admits a Turing instability iff it admits no Turing–Hopf instability and

$$\tilde a_3=-d_1d_2d_3,\quad \tilde a_2=d_1d_2J_{33}+d_2d_3J_{11}+d_3d_1J_{22},\quad \tilde a_1=-\big[d_1M_{23}+d_2M_{31}+d_3M_{12}\big],\quad \tilde a_0=\det J$$

satisfy (P1).

## Depends on

- [Turing patterns and diffusion-driven instability](../turing-patterns-and-diffusion-driven-instability/README.md)

## Expansion

The characteristic polynomial of $J(k^2)$ is $\lambda^3-c_2\lambda^2+c_1\lambda-c_0$ with $c_2=\mathrm{tr}J(k^2)<0$. By Routh–Hurwitz, with $c_2<0$ a real positive root exists iff $c_0=\det J(k^2)>0$, and a complex pair with positive real part iff $c_1>0$ and $c_2c_1>c_0$. As functions of $y=k^2$, $\det J(y)=\tilde a_3y^3+\dots+\tilde a_0$ and $c_2c_1-c_0=g(y)$ are cubics and $c_1=h(y)$ is a quadratic, with signs at $0$ and $\infty$ fixed by stability of the kinetics and positivity of the $d_i$. The theorem is then the elementary question of when a cubic, or a cubic and a quadratic simultaneously, are positive somewhere on $(0,\infty)$, answered by the location of the cubic's local maximum.

## Sources

- V. Piskovsky, "Turing instabilities for three interacting species", *Applied Mathematics Letters* 159 (2025), 109269, Theorem 1, Lemmas 1–5, conditions (polynom_cond1) and (polynom_cond2), <https://doi.org/10.1016/j.aml.2024.109269> (preprint arXiv:2405.14682).
