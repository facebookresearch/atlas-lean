# Supercritical pitchfork and stability of the first adhesion branch

**Setting.** Steady states $u'' = \alpha\,(u\,\mathcal K[u])'$ of the nonlocal adhesion model on $S^1_L$, $L>2$, with linear adhesion $h(u)=u$, mean $\bar u>0$, odd kernel $\Omega(r) = \operatorname{sign}(r)\omega(r)$, sine coefficients $M_n(\omega) = \int_0^1 \sin(2\pi n r/L)\,\omega(r)\,dr$, and bifurcation values $\alpha_n = n\pi/(\bar u L M_n(\omega))$.

**Theorem (bifurcation type).** Near $(\alpha_n,\bar u)$ the bifurcating branch has the expansion

$$\begin{pmatrix} u_n(x,s)\\ \alpha_n(s)\end{pmatrix} = \begin{pmatrix}\bar u\\ \alpha_n\end{pmatrix} + s\begin{pmatrix}\alpha_n\\ 0\end{pmatrix}\cos\!\Big(\frac{2\pi n x}{L}\Big) + s^2\begin{pmatrix} p_1(x)\\ \alpha_{3,n}\end{pmatrix} + o(s^2),$$

so $\alpha_n'(0)=0$ and the bifurcation is a pitchfork. Its direction is the sign of

$$\alpha_{3,n} = \frac{1}{4\bar u^5}\Big(\frac{\pi n}{L}\Big)^3\Big[M_n(\omega)^2\big(2M_n(\omega) - M_{2n}(\omega)\big)\Big]^{-1},$$

i.e. it is supercritical exactly when $\Delta M_n := 2M_n(\omega) - M_{2n}(\omega) > 0$.

**Corollary (uniform kernel).** If $\omega \equiv \tfrac12$ and $M_n(\omega)>0$, then $\Delta M_n > 0$: only supercritical pitchforks occur. In particular the $n$-th bifurcation is supercritical whenever $n < L/2$, so the first bifurcation is always supercritical.

**Stability.** For $s \ne 0$ small, the eigenvalue of smallest modulus of the linearization at $u_n(\cdot,s)$, within the mass class $\{\text{mean} = \bar u\}$, has the sign opposite to $\alpha_{3,n}$. For the uniform kernel the first branch is linearly asymptotically stable near $(\alpha_1,\bar u)$, while all higher branches are saddles.

## Depends on

- [Global bifurcation of spiky steady states of the nonlocal adhesion model](global-bifurcation-of-spiky-steady-states-of-the-nonlocal-adhesion-model.md)

## Expansion

$\mathcal K$ is skew-adjoint on $L^2(S^1_L)$ and acts diagonally on Fourier modes, $\mathcal K[\sin(2\pi n x/L)] = 2M_n\cos(2\pi n x/L)$ and $\mathcal K[\cos(2\pi n x/L)] = -2M_n\sin(2\pi n x/L)$. The quadratic nonlinearity $(u\mathcal K[u])'$ couples mode $n$ only to modes $0$ and $2n$, so the second-order correction $p_1$ lives in mode $2n$, and solvability at third order gives $\alpha_{3,n}$ with the factor $2M_n - M_{2n}$. Crandall–Rabinowitz exchange of stability then ties the sign of the critical eigenvalue to the bending direction of the branch.

## Sources

- Andreas Buttenschön and Thomas Hillen, "Non-Local Cell Adhesion Models: Steady States and Bifurcations", arXiv:2001.00286 (2020); chapter "Global Bifurcation": bifurcation-type theorem with the formula for $\alpha_{3,n}$, the corollaries on supercriticality for the uniform kernel, the eigenvalue-sign theorem and the stability corollary for the first branch, <https://doi.org/10.48550/arXiv.2001.00286>.
