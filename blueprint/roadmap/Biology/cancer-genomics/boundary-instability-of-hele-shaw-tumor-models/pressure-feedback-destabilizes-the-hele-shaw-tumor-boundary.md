# Pressure feedback destabilizes the Hele–Shaw tumor boundary

**Model.** Take the incompressible limit $m\to\infty$ of the porous-medium tumor model $\partial_t\rho-\nabla\cdot(\rho\nabla p)=\rho\,\Phi(p,c)$ with $p=\rho^m$, growth law $\Phi(p,c)=c/c_B-p/p_M$, and a quasi-static nutrient. The tumor becomes a patch $\rho=\chi_{\Omega(t)}$ whose boundary moves by Darcy's law. With the pressure-feedback parameter $\gamma:=1/p_M>0$, set by the homeostatic pressure, and nutrient consumption rate $\lambda>0$:

$$\begin{aligned}
-\Delta p+\gamma p&=c^{(i)}/c_B\ \text{in }\Omega(t), & p&=0\ \text{on }\partial\Omega(t), & V_n&=-\nabla p\cdot n\ \text{on }\partial\Omega(t),\\
-\Delta c^{(i)}+\lambda c^{(i)}&=0\ \text{in }\Omega(t), & -\Delta c^{(o)}+c^{(o)}&=c_B\ \text{outside}, & c,\ \partial_nc&\ \text{continuous across }\partial\Omega(t).
\end{aligned}$$

The case $\gamma=0$ is the model without pressure feedback.

**Finite-radius tumors.** Perturb a disk of radius $R$ by a single Fourier mode $\cos(l\theta)$, and let $\mathcal F_l(R;\lambda,\gamma)$ be the linear growth rate of mode $l$ relative to the radius.

1. The translation mode is neutral: $\mathcal F_1\equiv0$.
2. For every $l\ge2$, $\lim_{R\to0^+}\mathcal F_l=\frac{1-l}{2}<0$, while

$$\mathcal F_l(R;\lambda,\gamma)=\frac{l^2-1}{2(\sqrt\lambda+1)(\sqrt\lambda+\sqrt\gamma)\,R^2}+O(R^{-3})\quad(R\to\infty).$$

Hence every mode $l\ge2$ changes sign at least once: small tumors are stable, and each mode eventually becomes unstable as the tumor grows.
3. For fixed $R$, $\mathcal F_l=\frac{\partial_rp_0(R)}{R}\,l+O(1)$ as $l\to\infty$, where $p_0$ is the radial pressure and $\partial_rp_0(R)<0$. So sufficiently high modes are always stable.
4. The limits $\gamma\to0$ and $R\to\infty$ do not commute:

$$\lim_{\gamma\to0}\lim_{R\to\infty}R^2\mathcal F_l=\frac{l^2-1}{2\sqrt\lambda(\sqrt\lambda+1)}>0,\qquad \lim_{R\to\infty}\lim_{\gamma\to0}R^2\mathcal F_l=\frac{(l^2-1)(\sqrt\lambda-1)}{2\lambda(\sqrt\lambda+1)} .$$

Without feedback, large tumors are stable for $\lambda\le1$. Any positive feedback $\gamma>0$, however small, makes them unstable.

**Planar traveling fronts.** Let $\mathcal E_l(\lambda,\gamma)$ be the growth rate of a transverse mode with wavenumber $l$ on a planar front.

5. $\mathcal E_0=0$. As $l\to0$, $\mathcal E_l=\frac{l^2}{2(\sqrt\lambda+1)(\sqrt\lambda+\sqrt\gamma)}+O(l^4)$, and as $l\to\infty$, $\mathcal E_l=-\frac{l}{(\sqrt\lambda+1)(\sqrt\lambda+\sqrt\gamma)}+\frac{1}{\sqrt\lambda+1}+O(l^{-1})$. The dispersion curve has a unique positive zero $l_*$, with long waves unstable and short waves stable.
6. For an integer $l\ge1$, let $\lambda_0^l>l^2$ be the stability threshold at $\gamma=0$. For $0<\lambda<\lambda_0^l$ there is a unique $\gamma_l^*(\lambda)>0$ such that $\mathcal E_l<0$ for $\gamma<\gamma_l^*$ and $\mathcal E_l>0$ for $\gamma>\gamma_l^*$, with transversal crossing $\partial_\gamma\mathcal E_l(\lambda,\gamma_l^*)>0$.
7. *(Bifurcation.)* At $\gamma=\gamma_l^*(\lambda)$ a local curve of nonsymmetric traveling-wave profiles $f_l(\epsilon)=\epsilon\cos(ly)+o(\epsilon)$ in $X_1^{3+\alpha}(\mathbb R)$ bifurcates from the planar front.

Pressure-dependent growth inhibition alone does not stabilize an advancing tumor interface; increasing the feedback can trigger fingering.

## Expansion

The radial base state solves modified Bessel equations: $c^{(i)}\propto I_0(\sqrt\lambda r)$, $c^{(o)}=c_B-\mathrm{const}\cdot K_0(r)$, and $p_0$ is built from $I_0(\sqrt\gamma r)$ and the nutrient. A mode-$l$ perturbation solves the same equations with $I_l,K_l$. Matching the Dirichlet condition for $p$ and the transmission conditions for $c$ on the perturbed boundary gives $\mathcal F_l$ as an explicit Bessel-function ratio. The large-$R$ asymptotics follow from uniform expansions of $I_l,K_l$, with $\sqrt\lambda$ and $\sqrt\gamma$ appearing as the decay rates of the nutrient and pressure boundary layers. In the planar case the Bessel functions become exponentials, which gives closed forms. The bifurcation uses the Crandall–Rabinowitz theorem on the traveling-front functional equation $F(f,\gamma)=0$ in Hölder spaces $X_1^{3+\alpha}\to X_1^{2+\alpha}$. The kernel of the Fréchet derivative $F_f(0,\gamma_l^*)$ is spanned by $\cos(ly)$, its range has codimension one, and the transversality condition is item 6.

These are the two propositions of the finite-radius analysis, the traveling-wave proposition, the Fréchet-derivative proposition, and the bifurcation theorem of the source.

## Sources

- Y. Feng, Y. Zhang, K. Zhou, "Tumor boundary instability induced by pressure feedback", arXiv:2608.30796 (2026). <https://doi.org/10.48550/arXiv.2608.30796>
