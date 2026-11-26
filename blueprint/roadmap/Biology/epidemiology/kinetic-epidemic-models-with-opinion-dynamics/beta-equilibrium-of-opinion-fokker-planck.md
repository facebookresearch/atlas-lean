# Beta equilibrium of the Fokker-Planck opinion model with compromise and bounded self-thinking

This page covers the opinion-formation component of Zanella (2023), Section 2.2, which follows the kinetic opinion model of Toscani (2006).

**Binary interactions.** Opinions lie in $I = [-1, 1]$ ($w = 1$: full agreement with protective behaviour). Two agents of the same compartment with opinions $(w, w_*)$ update to

$$w' = w + \lambda P(w, w_*)(w_* - w) + D(w)\eta, \qquad w'_* = w_* + \lambda P(w_*, w)(w - w_*) + D(w_*)\tilde\eta,$$

with compromise rate $\lambda \in (0,1)$, interaction function $P \in [0,1]$, local diffusion $D \ge 0$, and i.i.d. centred noises of variance $\sigma^2$. For symmetric $P$ the mean opinion is conserved in each interaction on average. The update stays in $I$ if $|\eta| \le c(1 - \lambda)$ and $c\, D(w) \le 1 - |w|$ for some $c > 0$, which forces $D(\pm 1) = 0$.

**Quasi-invariant limit.** With $P \equiv 1$, scaling $\lambda \to \epsilon\lambda$, $\sigma^2 \to \epsilon\sigma^2$, rescaling time by $\epsilon$ and letting $\epsilon \to 0^+$ (assuming a finite third moment of $\eta$), the Boltzmann-type model for the opinion density $f(w,t)$ with mass $\rho$ and mean $m$ converges to the Fokker-Planck equation

$$\partial_t f = \partial_w\Big[ \lambda (w - m) f + \frac{\sigma^2}{2} \partial_w\big( D^2(w) f \big) \Big] \qquad (11)$$

with no-flux boundary conditions at $w = \pm 1$. (Here the mass $\rho$ of the compartment is absorbed into $\lambda$, as in the source.)

**Equilibrium (eqs. (12)-(13)).** For $D(w) = \sqrt{1 - w^2}$ and $\nu = \sigma^2/\lambda$, the steady state with unit mass and mean $m \in (-1,1)$ is the beta density

$$f^\infty(w) = \frac{(1+w)^{\frac{1+m}{\nu} - 1}(1-w)^{\frac{1-m}{\nu} - 1}}{2^{\frac{2}{\nu} - 1} B\big( \frac{1+m}{\nu}, \frac{1-m}{\nu} \big)}, \qquad w \in (-1, 1),$$

with moments

$$\int_{-1}^1 w f^\infty\, dw = m, \qquad \int_{-1}^1 w^2 f^\infty\, dw = \frac{\nu}{2 + \nu} + \frac{2}{2 + \nu} m^2 .$$

For $m = 0$ the density is unimodal at $0$ (consensus) when $\nu < 1$ and U-shaped, concentrating at $\pm 1$ (polarization), when $\nu > 1$.

## Expansion

A stationary zero-flux solution of (11) satisfies $\lambda(w - m) f + \tfrac{\sigma^2}{2}\big((1 - w^2) f\big)' = 0$. With $g = (1 - w^2) f$, $g'/g = -\tfrac{2}{\nu}\tfrac{w - m}{(1-w)(1+w)} = \tfrac{1+m}{\nu}\tfrac{1}{1+w} - \tfrac{1-m}{\nu}\tfrac{1}{1-w}$, so $g \propto (1+w)^{(1+m)/\nu}(1-w)^{(1-m)/\nu}$ and $f = g/(1 - w^2)$. Equivalently $(1 + w)/2 \sim \mathrm{Beta}(a, b)$ with $a = (1+m)/\nu$, $b = (1-m)/\nu$; then $\mathbb{E}w = 2a/(a+b) - 1 = m$ and $\mathrm{Var}\, w = 4ab/\big((a+b)^2(a+b+1)\big) = \nu(1 - m^2)/(\nu + 2)$, which gives the second moment. Both exponents are negative, giving the U shape, exactly when $\nu > 1 + |m|$.

## Sources

- M. Zanella, Kinetic models for epidemic dynamics in the presence of opinion polarization, *Bull. Math. Biol.* 85 (2023), <https://doi.org/10.1007/s11538-023-01147-2>, PMCID PMC10052322.
- G. Toscani, Kinetic models of opinion formation, *Commun. Math. Sci.* 4 (2006), 481-496, <https://doi.org/10.4310/CMS.2006.v4.n3.a1>.
