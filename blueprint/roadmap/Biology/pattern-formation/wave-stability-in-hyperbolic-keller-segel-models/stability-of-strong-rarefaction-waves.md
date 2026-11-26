# Nonlinear stability of strong rarefaction waves in the hyperbolic Keller–Segel model

The Levine–Sleeman–Nilsen-Hamilton angiogenesis model with logarithmic sensitivity, $n_t=Dn_{xx}-\chi(n(\ln c)_x)_x$, $c_t=-nc+\beta c$, describes endothelial cell density $n>0$ and VEGF concentration $c>0$. The Hopf–Cole-type substitution $q=-(\ln c)_x$ followed by rescaling turns it into the parabolic–hyperbolic system

$$n_t-(nq)_x=n_{xx},\qquad q_t-n_x=0,\qquad x\in\mathbb R,\ t>0,$$

with $(n,q)(x,0)\to(n_\pm,q_\pm)$ as $x\to\pm\infty$, $n_\pm>0$. The inviscid part $n_t-(nq)_x=0$, $q_t-n_x=0$ is strictly hyperbolic on $\{n>0\}$, with eigenvalues $\lambda_{1,2}(n,q)=\tfrac12\big(-q\mp\sqrt{q^2+4n}\big)$, right eigenvectors $r_k=(-\lambda_k,1)^{\mathsf T}$, and genuinely nonlinear characteristic fields.

For $k\in\{1,2\}$ let $R_k(n_-,q_-)=\{(n,q)\in\Gamma_k:\lambda_k(n,q)\ge\lambda_k(n_-,q_-)\}$ be the $k$-rarefaction branch along the maximal integral curve $\Gamma_k$ of $r_k$ through $(n_-,q_-)$ in $\{n>0\}$. Let $(n^r_k,q^r_k)$ be the smooth approximate $k$-rarefaction wave obtained from the Burgers equation $w_t+ww_x=0$ with initial datum

$$w_{k0}(x)=\tfrac12\big(\lambda_k^++\lambda_k^-\big)+\tfrac12\big(\lambda_k^+-\lambda_k^-\big)\kappa_\theta\int_0^{\varepsilon x}(1+y^2)^{-\theta}\,dy,\qquad\lambda_k^\pm=\lambda_k(n_\pm,q_\pm),$$

with initial value $(N_{k0},Q_{k0})$, where $\kappa_\theta$ normalizes the integral to $\pm1$ at $\pm\infty$.

**Theorem.** Fix $\theta>\tfrac32$, $k\in\{1,2\}$ and end states with $(n_+,q_+)\in R_k(n_-,q_-)$, $n_\pm>0$. The rarefaction may be **strong**: its amplitude $|n_+-n_-|$ is not required to be small. There are $\varepsilon_0,\delta_0>0$ such that for $0<\varepsilon\le\varepsilon_0$ and $\|(n_0-N_{k0},q_0-Q_{k0})\|_{H^1}\le\delta_0$ there is a unique global solution with $(n-n^r_k,q-q^r_k)\in C([0,\infty);L^2)$, $(n,q)_x\in C([0,\infty);L^2)$, $n_{xx}\in L^2(0,\infty;L^2)$, and

$$\lim_{t\to\infty}\sup_{x\in\mathbb R}\big|(n,q)(x,t)-(n^r_k,q^r_k)(x,t)\big|=0 .$$

The same conclusion holds for the composite wave formed by a 1-rarefaction followed by a 2-rarefaction, $(n_+,q_+)\in RR(n_-,q_-)$.

## Expansion

The proof is an $H^1$ energy method for the perturbation $(\phi,\psi)=(n-n^r_k,q-q^r_k)$. Positivity of $n$ and the relation $q^2+4n>0$ keep the system strictly hyperbolic along the wave. Genuine nonlinearity, $\nabla\lambda_k\cdot r_k\ne0$ (normalized to be positive), makes the rarefaction expansive, $\partial_x\lambda_k(n^r_k,q^r_k)>0$, which supplies the good dissipative terms $\int|Q_{kx}|\phi^2$ and $\int|N_{kt}|\psi^2$. Riemann invariants $h_k$ with $\nabla h_k\cdot r_k=0$ let the wave be built from one Burgers equation. Taking $\varepsilon$ small rather than the wave amplitude makes the source errors of the approximate wave small, since they are of order $\varepsilon$ in the weighted norms; the decay exponent $\theta>3/2$ makes these errors time-integrable. A uniform-in-$\varepsilon$ local existence result and the a priori estimate close by continuation.

## Sources

- Sitong Liu, Jingyu Li, "Asymptotic stability of strong rarefaction waves to a parabolic-hyperbolic system arising from chemotaxis", arXiv:2606.01559 (2026), Section 1 (system, eigenstructure, rarefaction branches $R_k$, approximate wave $w_{k0}$), Theorems 1.1–1.2, Propositions 3.1–3.2, <https://doi.org/10.48550/arXiv.2606.01559>.
