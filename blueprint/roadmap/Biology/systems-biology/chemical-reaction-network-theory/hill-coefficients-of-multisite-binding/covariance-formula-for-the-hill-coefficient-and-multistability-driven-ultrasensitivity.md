# Covariance formula for the Hill coefficient and multistability-driven ultrasensitivity

**Setting.** A macromolecule has $N$ binding (or phosphorylation) sites; a configuration is $n = (n_1,\dots,n_N) \in \{0,1\}^N$ with $|n| = \sum_i n_i$ occupied sites. At ligand concentration $v > 0$ the configuration has law

$$\pi(n) = \frac{\mu(n)\,v^{|n|}}{Z(v)}, \qquad Z(v) = \sum_n \mu(n)\,v^{|n|},$$

for non-negative weights $\mu$. For a non-negative increasing activity function $a$ on $[0,1]$ the response is $f(v) = \langle a(|n|/N)\rangle_\pi$, and the **Hill coefficient** is

$$\eta_H(v) = v\,\frac{d}{dv}\ln\frac{f(v)}{f(\infty) - f(v)}.$$

The system is ultrasensitive (of order $N$) when $\eta_H$ near the half-maximal concentration grows proportionally to $N$.

**Theorem (Hill coefficient as a covariance).** Let $k^*$ be the largest $k$ with $\mu(n) > 0$ for some $|n| = k$, so $a(k^*/N) = f(\infty)$. Then

$$\eta_H(v) = N\,\frac{\operatorname{Cov}_\pi\big(a(|n|/N),\,|n|/N\big)\,a(k^*/N)}{f(v)\,\big(a(k^*/N) - f(v)\big)},$$

Large Hill coefficients therefore require the fraction of bound sites to have non-vanishing variance at large $N$.

**Theorem (multistability and ultrasensitivity).** Let the number of bound sites be a density-dependent birth–death process on $\{0,\dots,N\}$ with rates $Nb^{(N)}(k/N)$ and $Nd^{(N)}(k/N)$, $b^{(N)}$ linear in $v$, $b^{(N)} - d^{(N)} \to F$ and $\ln(d^{(N)}/b^{(N)}) \to \ln r$, so that $X_N = Y_N/N$ follows $\dot x = F(x)$ in the limit and its stationary law $\bar\pi_N$ (of the above form) satisfies a large deviation principle with rate $I(x) = \int_0^x \ln r(u)\,du - \min_{[0,1]}\int_0^{\cdot}\ln r$. Assume the source's Assumption 4 in full:

- (4.1) $\dot x = F(x)$ has finitely many equilibria $x_1,\dots,x_m$, and $I(x_i)=0$, $I'(x_i)=0$ and $I''>0$ in a neighbourhood of each $x_i$;
- (4.2) $\int_0^1|\ln r(u)|\,du < \infty$ (27);
- (4.3) the limiting birth and death rates $b$, $d$ satisfy $b(x)/(1-x)\to\ell_{b,0}$ and $d(x)/x\to\ell_{d,0}$ as $x\to0^+$, and $b(x)/(1-x)\to\ell_{b,1}$ and $d(x)/x\to\ell_{d,1}$ as $x\to1^-$, with four positive constants $\ell_{b,0},\ell_{b,1},\ell_{d,0},\ell_{d,1}$;
- (4.4) $r$ is left-continuous on $(0,1)$ and piecewise $C^2$: $r$, $r'$ and $r''$ have finitely many discontinuities in $(0,1)$;
- (4.5) $M = \limsup_{N\to\infty} \max_{1\le j\le N}\bigl(\sum_{k=1}^{j}\ln\frac{d^{(N)}(k/N)}{b^{(N)}(k/N)} - \sum_{k=1}^{j}\ln r(k/N)\bigr)$ is finite (28).

For continuous, bounded, strictly increasing $a$:

1. if $I$ has a unique minimizer $x_1$ in the interior, then $\eta_H(v)/N \to 0$ (monostable systems are not ultrasensitive of order $N$);
2. if at some critical concentration $v_c$ the function $I$ attains its minimum at two distinct points $x_1 \ne x_2$, then

$$\liminf_{N\to\infty}\frac{\eta_H(v_c)}{N} > 0,$$

and the system is ultrasensitive of order $N$; then $\bar\pi_N$ converges weakly to a mixture $\sum_i c_i\delta_{x_i}$ of point masses at the minimizers.

**Sharp thresholds.** For increasing events $A$ of a site process whose law is monotone and invariant under a transitive group of site permutations, $\frac{d}{dp}\mu_p(A) \ge \frac{c\,\alpha_p}{p(1-p)}\min\{\mu_p(A),1-\mu_p(A)\}\ln N$, a Friedgut–Kalai-type bound that yields switch-like responses as $N$ grows.

## Expansion

Differentiating $\ln f$ and $\ln(f(\infty) - f)$ in $v$ brings down $|n|$ from $v^{|n|}$, so $v f'(v) = \operatorname{Cov}_\pi(a(|n|/N), |n|)$; substituting into the definition gives the covariance formula. In the birth–death picture the stationary law concentrates where $I$ vanishes: with a single minimizer the fraction of bound sites has variance $O(1/N)$ and the covariance stays $O(1/N)$, so $\eta_H = o(N)$; at a concentration where two stable equilibria have equal "free energy" the stationary law splits its mass between them, the variance stays of order one, and $\eta_H$ grows like $N$. Allosteric (Monod–Wyman–Changeux-type) phosphorylation models give an explicit binomial mixture with $v_c = 1/\sqrt{\varepsilon}$ and closed-form limits of $\eta_H$ away from $v_c$.

## Sources

- Michaël Dougoud, Christian Mazza and Laura Vinckenbosch, "Ultrasensitivity and sharp threshold theorems for multisite systems", arXiv:1511.03150 (2015), Theorems 1, 2 and 5, Assumption 4, Corollary 12 and Proposition 7, <https://doi.org/10.48550/arXiv.1511.03150>. Published version: Journal of Physics A: Mathematical and Theoretical 50 (2017) 075601, <https://doi.org/10.1088/1751-8121/aa54e3>.
