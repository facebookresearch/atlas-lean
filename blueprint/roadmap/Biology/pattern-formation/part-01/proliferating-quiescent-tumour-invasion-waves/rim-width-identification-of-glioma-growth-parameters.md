# Rim-width identification of glioma growth parameters

**Setting.** In the proliferating–quiescent glioma model with diffusion coefficient $D$, birth rate $\rho$ and quiescence rate $k$, the approximate travelling-wave profile gives the proliferating density as a function $p(w)$ of free space, obtained by integrating $dp/dw=\delta(w)/(\hat\rho\,g(w))-1$ with $\hat\rho=\rho/k$. Let $p_{\max}=\max p$, and let $0<a_2<a_1<1$ be the detection thresholds of contrast-enhanced T1 and T2 magnetic resonance imaging, so T1 shows $p\ge a_1p_{\max}$ and T2 shows $p\ge a_2p_{\max}$. Define $w_1^\pm$ and $w_2$ by $p(w_1^\pm)=a_1p_{\max}$ and $p(w_2)=a_2p_{\max}$.

**Estimator.** In dimensional form the enhancing (proliferating) rim width and the edematous rim width are

$$\ell_1=2\sqrt{\frac{D\rho}{k^2}}\int_{w_1^-}^{w_1^+}\frac{dz}{dw}\,dw,\qquad
\ell_2=2\sqrt{\frac{D\rho}{k^2}}\int_{w_2}^{w_1^-}\frac{dz}{dw}\,dw,$$

and the front speed is $c=2\sqrt{\rho D}$. Matching to image-derived rim widths $L_1,L_2$ and speed $V$ gives three equations $\ell_1=L_1$, $\ell_2=L_2$, $c=V$ in $(D,\rho,k)$. Their ratio eliminates the dimensional prefactor:

$$f(\hat\rho)\equiv\frac{\int_{w_1^-}^{w_1^+}(dz/dw)\,dw}{\int_{w_2}^{w_1^-}(dz/dw)\,dw}=\frac{L_1}{L_2}.$$

If $f$ is strictly monotone, this equation has at most one root $\hat\rho=\rho/k$; back-substitution into $\ell_1=L_1$ then gives $\rho/D$, and $c=V$ fixes $\rho$, hence $D$ and $k$. The three parameters are then identifiable from rim widths and speed.

**Single scan.** Without a second scan to measure $V$, assume the tumour grows exponentially from a point source of density $p_0$ (quiescence negligible) up to time $t^*$, then as a wave. The T1 and T2 radii $R_1,R_2$ must then imply the same tumour age:

$$\frac{R_1-R_1^*}{2\sqrt{\rho D}}=\frac{R_2-R_2^*}{2\sqrt{\rho D}},\qquad
R_i^*=\sqrt{t^*\Big(4D\rho\,t^*-4D\ln\big(a_i(4\pi Dt^*)^{3/2}/p_0\big)\Big)},\quad i=1,2,$$

which replaces $c=V$ as the third equation.

## Depends on

- [Travelling waves of the proliferating–quiescent glioma model](travelling-waves-of-the-proliferating-quiescent-glioma-model.md)

## Expansion

Identifiability rests entirely on the monotonicity of $f$. The source checks it numerically for birth and quiescence functions taken from the beta CDF family, $g(w)=B(w;\alpha_g,\beta_g)$ and $\delta(w)=1-B(w;\alpha_\delta,\beta_\delta)$, which covers linear, sigmoidal and concave shapes; it does not prove it in general. The rim widths come from the reduced profile, in which the scale-invariant shape depends only on $g$, $\delta$ and $\hat\rho$, while $D$ enters only through the length scale and the speed. $R_i^*$ is the radius at which the Gaussian density $p_0e^{\rho t}(4\pi Dt)^{-3/2}e^{-r^2/(4Dt)}$ crosses the threshold $a_i$ at $t=t^*$.

## Sources

- L. Han, S. Eikenberry, C. He, L. Johnson, M. C. Preul, E. J. Kostelich, Y. Kuang, "Patient-specific parameter estimates of glioblastoma multiforme growth dynamics from a model with explicit birth and death rates", *Mathematical Biosciences and Engineering* (2019), Section 2.3, Eqs. (2.10)–(2.14), Eq. (4.4), Section 3 and Figure 4, <https://doi.org/10.3934/mbe.2019265>, PMCID PMC7304543.
