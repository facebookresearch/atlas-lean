# $L^\infty$ bound for Fokker–Planck equations with a semiconvex drift potential

**Setting.** On $\mathbb{R}^d$ consider the drift–diffusion equation with absorption

$$\partial_t \rho - \Delta \rho + \nabla\cdot(\rho\,\nabla \Phi(x,t)) = -h(x,t)\,\rho ,\qquad \rho(\cdot,0)=\rho_0 ,$$

where $h\in L^\infty(\mathbb{R}^d\times[0,\infty))$ is nonnegative, $\Phi(\cdot,t)$ is $H^2_{\mathrm{loc}}$ in space for every $t$, and $\nabla\Phi$ is bounded on $\mathbb{R}^d\times[0,\infty)$. In chemotaxis applications $\Phi=\chi(-\Delta)^{-1}\rho_2$ is the potential of an attractant secreted by a second density $\rho_2\ge 0$, and $h=\epsilon\rho_2$ is a reaction (consumption) rate.

**Theorem.** Let $\rho_0\in L^1(\mathbb{R}^d)\cap L^\infty(\mathbb{R}^d)$. If there is $\gamma>0$ with $\Delta\Phi(\cdot,t)\ge-\gamma$ for all $t\ge 0$, then for all $t\ge0$

$$\|\rho(\cdot,t)\|_{L^\infty}\le C(d)\,\max\{t^{-d/2},\ \gamma^{d/2}\}\,\|\rho_0\|_{L^1},$$

with a constant $C(d)$ depending only on the dimension.

For an attracting potential $\Phi=\chi(-\Delta)^{-1}g$ with $0\le g\le \|g\|_\infty$ one has $\Delta\Phi=-\chi g\ge -\chi\|g\|_\infty$, so the hypothesis holds with $\gamma=\chi\|g\|_\infty$. The bound says the density cannot concentrate beyond the scale $\gamma^{d/2}$ set by the strength of the attraction, uniformly in time.

**Consequence (global regularity).** For the chemotaxis–reaction system

$$\partial_t\rho_1-\Delta\rho_1+\chi\nabla\cdot\big(\rho_1\nabla(-\Delta)^{-1}\rho_2\big)=-\epsilon\rho_1\rho_2,\qquad \partial_t\rho_2=-\epsilon\rho_1\rho_2 ,$$

nonnegative initial data in $L^1(\mathbb{R}^d)\cap H^m(\mathbb{R}^d)$ with an integer $m>d/2$ give a global solution $(\rho_1,\rho_2)\in C\big([0,\infty);L^1\cap H^m\big)$. Unlike the single-species Keller–Segel equation, no finite-time blow-up occurs, because the attractant is produced by the immobile, nonincreasing density $\rho_2$.

## Expansion

Write the equation as $\rho_t-\Delta\rho+\nabla\Phi\cdot\nabla\rho=-(h+\Delta\Phi)\rho\le\gamma\rho$ and follow the Carlen–Loss proof of $L^1\to L^\infty$ smoothing: the $L^1$ norm is nonincreasing (the drift term is a divergence, $h\ge0$), while the $L^2$ norm satisfies $\frac{d}{dt}\|\rho\|_2^2\le-2\|\nabla\rho\|_2^2+\gamma\|\rho\|_2^2$, and the Nash inequality $\|\rho\|_2^{1+2/d}\le C\|\rho\|_1^{2/d}\|\nabla\rho\|_2$ turns this into $L^1\to L^2$ smoothing with the rate $\max\{t^{-d/4},\gamma^{d/4}\}$. Duality gives $L^2\to L^\infty$, and composing the two half-steps yields the stated $L^1\to L^\infty$ estimate. Global existence then follows from a standard $H^m$ energy estimate for the $\rho_1$ equation, using the $L^\infty$ control and the product bound $\|f\nabla(-\Delta)^{-1}g\|_{H^m}\le C(\|g\|_1+\|g\|_\infty)\|f\|_{H^m}+C\|f\|_\infty\|g\|_{H^m}$.

## Sources

- Alexander Kiselev, Fedor Nazarov, Lenya Ryzhik, Yao Yao, "Chemotaxis and Reactions in Biology", arXiv:2004.06441 (2020): Theorem 3.1 ($L^\infty$ bound), Lemma 3.2 (product estimate), Theorem 3.3 (global regularity), Section 3. <https://doi.org/10.48550/arXiv.2004.06441>. Published version: Journal of the European Mathematical Society 25(7) (2022), 2641–2696, <https://doi.org/10.4171/jems/1247>; locators above refer to the arXiv version.
