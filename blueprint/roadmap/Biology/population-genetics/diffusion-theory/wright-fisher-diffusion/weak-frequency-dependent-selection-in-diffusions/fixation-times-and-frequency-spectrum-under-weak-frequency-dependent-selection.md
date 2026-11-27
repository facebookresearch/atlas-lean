# Fixation times and frequency spectrum under weak frequency-dependent selection

**Setting.** As in [fixation probability under weak frequency-dependent selection](fixation-probability-under-weak-frequency-dependent-selection.md), $X$ solves $dX = \alpha\psi(X)\sigma^2(X)\,dt + \sigma(X)\,dW$ on $[0,1]$ until $T = T_0 \wedge T_1$. Write $\mathbf E^{\alpha *}_{0+}[T_1]$ for the expected fixation time conditioned on fixation and started from $0+$, $\mathbf E^\alpha_{x*}[T_0]$ for the expected extinction time conditioned on extinction, and

$$f^\alpha(x) = \frac{e^{2\alpha\int_0^x \psi(y)\,dy}}{\sigma^2(x)}\,\mathbf P^\alpha_x(T_0 < T_1)$$

for the density of the expected **frequency spectrum** (expected number of alleles at frequency $x$ when new mutants enter at rate $\theta$ near frequency 0, up to the factor $\theta$).

**Theorem.** If all integrals exist:
1. (Conditional fixation time, Theorem 3)

$$\lim_{\alpha\to 0}\frac{1}{4\alpha}\Big(\mathbf E^{\alpha*}_{0+}[T_1] - 2\int_0^1 \frac{(1-y)y}{\sigma^2(y)}\,dy\Big) = \int_0^1 \frac{1}{\sigma^2(y)}\Big((1-y)^2\int_0^y z\,\psi(z)\,dz - y^2\int_y^1 (1-z)\,\psi(z)\,dz\Big)dy.$$

2. (Frequency spectrum, Theorem 5)

$$\lim_{\alpha\to 0}\frac{1}{2\alpha}\Big(f^\alpha(x) - \frac{1-x}{\sigma^2(x)}\Big) = \frac{x}{\sigma^2(x)}\Big(\frac1x\int_0^x (1-y)\,\psi(y)\,dy - \int_0^1 (1-y)\,\psi(y)\,dy\Big).$$

3. (Constant and linear selection, Corollaries 2.3 and 2.5) For $\psi \equiv 1$ the first-order change of $\mathbf E^{\alpha*}_{0+}[T_1]$ vanishes, and $\partial_\alpha f^\alpha(x)|_{\alpha=0} = x(1-x)/\sigma^2(x)$. For $\psi(x) = x$, $\partial_\alpha \mathbf E^{\alpha*}_{0+}[T_1]|_{\alpha=0} = -\frac23\int_0^1 y^2(1-y)^2/\sigma^2(y)\,dy < 0$ and $\partial_\alpha f^\alpha(x)|_{\alpha=0} = -x(1-x)(1-2x)/(3\sigma^2(x))$.

Theorems 2 and 4 give the analogous first-order expansions, as $x \to 0$, of the unconditional absorption time and of the extinction time conditioned on extinction.

## Depends on

- [Fixation probability under weak frequency-dependent selection](fixation-probability-under-weak-frequency-dependent-selection.md)

## Expansion

All quantities are explicit functionals of the scale function and speed measure of a one-dimensional diffusion, so each expansion is a first-order Taylor expansion of Green's-function formulas in $\alpha$. For the Wright–Fisher case $\sigma^2(y) = y(1-y)$, the neutral conditional fixation time from $0+$ is $2$ (in diffusion time units), and under constant selection it is unchanged to first order, the classical symmetry between beneficial and deleterious mutants conditioned on fixation. Frequency dependence breaks this symmetry: when the advantage $\psi$ increases with frequency, a mutant that fixes does so faster on average than a neutral one, consistent with the counter-intuitive observation that selection can shorten fixation times conditioned on fixation. The spectrum correction shows how frequency-dependent selection reshapes the site frequency spectrum $1/x$ of the neutral Wright–Fisher model.

## Sources

- Peter Pfaffelhuber and Anton Wakolbinger, "Fixation probabilities and hitting times for low levels of frequency-dependent selection", *Theor. Popul. Biol.* 124 (2018), 61-69. <https://doi.org/10.1016/j.tpb.2018.09.003>
- Preprint version (the locators in this item follow its numbering): Peter Pfaffelhuber and Anton Wakolbinger, "Fixation probabilities and hitting times for low levels of frequency-dependent selection", arXiv:1801.01584 (2018), Section 1, Theorems 2–5, Corollaries 2.3 and 2.5, <https://doi.org/10.48550/arXiv.1801.01584>.
