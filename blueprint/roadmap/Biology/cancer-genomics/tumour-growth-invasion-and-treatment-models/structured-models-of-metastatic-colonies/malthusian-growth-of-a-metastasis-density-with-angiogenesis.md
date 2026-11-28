# Malthusian growth of a two-dimensional metastasis density with angiogenesis

**Model.** Each metastasis is described by its size $x$ and its angiogenic capacity $\theta$ (the carrying capacity set by its vasculature), and grows by the Hahnfeldt–Panigrahy–Folkman–Hlatky dynamics

$$\dot X=G(X),\qquad G(x,\theta)=\Big(ax\ln\frac{\theta}{x},\ cx-d\theta x^{2/3}\Big),$$

restricted to the square $\Omega=(1,b)^2$, on whose boundary $\Gamma$ the field $G$ points inward and vanishes at the corner $(b,b)$. The density $\rho(t,x,\theta)$ of metastases satisfies the transport equation with a nonlocal birth boundary condition

$$\begin{cases}\partial_t\rho+\operatorname{div}(G\rho)=0,& (x,\theta)\in\Omega,\\[2pt]
-G\cdot\nu\,\rho(t,\sigma)=N(\sigma)\displaystyle\int_\Omega\beta(x,\theta)\rho(t,x,\theta)\,dx\,d\theta+f(t,\sigma),&\sigma\in\Gamma,\\[2pt]
\rho(0,\cdot)=\rho^0,\end{cases}$$

where $\beta$ is the emission rate of new metastases, $N$ the distribution of their birth sizes on $\Gamma$, and $f$ the emission by the primary tumor. The standing hypotheses (9) of the source are

$$\beta\in L^\infty(\Omega),\ \beta\ge0\text{ a.e.},\qquad N\in\mathrm{Lip}(\Gamma),\ N\ge0,\ \operatorname{supp}N\text{ compact in }\Gamma^*=\Gamma\setminus\{(b,b)\},\qquad \int_\Gamma N=1 .$$

Let $\Phi_\tau(\sigma)$ denote the flow of $G$ started at $\sigma\in\Gamma$.

**Theorem.** Assume (9).

*(1)* (Well-posedness) For $\rho^0\in L^1(\Omega)$ and $f\in L^1((0,\infty)\times\Gamma)$ there is a unique weak solution $\rho=e^{tA}\rho^0+\mathcal Tf\in C([0,\infty);L^1(\Omega))$. Here $A$ generates a positive semigroup with $\|e^{tA}\|\le e^{t\|\beta\|_\infty}$; its natural domain uses the space $W^{\rm div}(\Omega)=\{V\in L^1:\operatorname{div}(GV)\in L^1\}$, and $\rho\ge0$ when $\rho^0,f\ge0$.

*(2)* (Malthus parameter) If $\int_0^\infty\int_\Gamma\beta(\Phi_\tau(\sigma))N(\sigma)\,d\sigma\,d\tau>1$, there is a unique $\lambda_0>0$ with

$$\int_0^\infty\int_\Gamma\beta(\Phi_\tau(\sigma))N(\sigma)e^{-\lambda_0\tau}\,d\sigma\,d\tau=1,$$

and a unique positive eigentriple $(\lambda_0,V,\Psi)$ of $A$ and $A^*$, with $V(\Phi_\tau(\sigma))=C\,N(\sigma)e^{-\lambda_0\tau}|J_\Phi(\tau,\sigma)|^{-1}$.

*(3)* (Asymptotic behavior) If moreover $\beta-\mu\Psi\ge0$ for some $\mu>0$, then with $m(t)=\int_\Omega\rho^0\Psi+\int_0^te^{-\lambda_0s}\int_\Gamma f\Psi$,

$$\big\|\rho(t)e^{-\lambda_0t}-m(t)V\big\|_{L^1_\Psi}\le e^{-\mu t}\Big(\|\rho^0-m(0)V\|_{L^1_\Psi}+2\int_0^te^{-(\lambda_0-\mu)s}\int_\Gamma|f|(s,\sigma)\Psi(\sigma)\,d\sigma\,ds\Big).$$

## Expansion

Along characteristics the problem reduces to a renewal equation for the boundary flux $B(t)=\int_\Omega\beta\rho$: a metastasis born at $\sigma$ at time $s$ sits at $\Phi_{t-s}(\sigma)$ at time $t$. The spectral equation is therefore an Euler–Lotka equation, in which the mean number of offspring along a lifetime trajectory must exceed one for exponential growth. The Jacobian factor $J_\Phi=G\cdot\nu\,\exp\int_0^\tau\operatorname{div}G(\Phi_s)\,ds$ converts time since birth into phase-space density. The weighted $L^1$ estimate is a generalized relative entropy argument for the adjoint eigenfunction $\Psi$; the condition $\beta\ge\mu\Psi$ gives a uniform spectral gap. The model extends Iwata–Kawasaki–Shigesada's one-dimensional colony-size equation by letting each colony carry its own vascular state, which vanishes at the stationary corner of $G$.

## Sources

- Sebastien Benzekry, "Mathematical analysis of a two-dimensional population model of metastatic growth including angiogenesis", arXiv:1009.2863 (2010), Section 2 (model, Proposition 2.1), Propositions 3.2–3.3, Corollary 3.1, Proposition 4.1, Theorem 4.1 and Proposition 4.3, <https://doi.org/10.48550/arXiv.1009.2863>.
