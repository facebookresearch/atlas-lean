# Travelling waves of Wolbachia spread in integro-difference models

**Setting.** Let $V_t(x)\in[0,1]$ be the frequency of *Wolbachia*-infected mosquitoes at location $x\in\mathbb R$ in generation $t$. With cytoplasmic incompatibility of intensity $s_h$, fecundity cost $s_f$ of infection ($0<s_f<s_h<1$) and maternal-transmission leakage $\mu$, local reproduction maps the infection frequency by

$$f(V)=\frac{(1-\mu)(1-s_f)\,V}{s_hV^2-(s_h+s_f)V+1}.$$

For $\mu=0$ this map is bistable, with stable fixed points $0$ and $1$ separated by the unstable invasion threshold $V_1^*=s_f/s_h$. Dispersal is modelled by a symmetric probability kernel $K$ (Gaussian, Laplace, exponential square-root or Cauchy), giving the *Wolbachia* integro-difference equation (WIDE)

$$V_{t+1}(x)=\int_{\mathbb R}K(x-y)\,f\bigl(V_t(y)\bigr)\,dy .$$

A travelling wave is a solution $V_t(x)=\phi(x-ct)$ with $\phi(-\infty)=1$, $\phi(+\infty)=0$.

**Theorem 2.1 (homogeneous states).** Every fixed point $V^*$ of $f$ is a spatially homogeneous equilibrium, and linearizing gives the dispersion relation $e^{\lambda(k)}=f'(V^*)\widehat K(k)$ with $\widehat K$ the Fourier transform of $K$; since $|\widehat K|\le1$, $V^*$ is linearly stable when $|f'(V^*)|<1$ and unstable when $f'(V^*)>1$.

**Theorem 3.4 (existence and uniqueness of the wave).** For $\mu=0$ there exist a non-increasing profile $\phi$ and a unique speed $c$ such that $\phi(x-ct)$ solves the WIDE with $\phi(-\infty)=1$, $\phi(+\infty)=0$; the profile is unique up to translation.

**Theorem 3.5 (speed formula).** For $\mu=0$, if $\phi$ is smooth with $\phi'<0$, $f$ is Lipschitz on $[0,1]$, $\phi'\in L^1(\mathbb R)$ and $\int|z|K(z)\,dz<\infty$, then

$$c=\int_0^1\frac{v-f(v)}{\phi'\bigl(\phi^{-1}(v)\bigr)}\,dv .$$

Equivalently (Proposition 4.1), $c=\lim_{t\to\infty}\frac1{V_2^*}\int_{\mathbb R}\bigl(V_{t+1}(x)-V_t(x)\bigr)dx$, with $V_2^*$ the stable infected state.

## Expansion

Integrating the profile equation $\phi(x-c)=\int K(x-y)f(\phi(y))\,dy$ over $x$, the left side minus $\int\phi$ equals $c$ times the jump $\phi(-\infty)-\phi(+\infty)=1$, while the right side minus $\int\phi$ equals $\int(f(\phi)-\phi)\,dy$ because $K$ has mass one; substituting $v=\phi(y)$ gives the speed formula. The sign of $c$ thus balances the gain region $v>V_1^*$, where $f(v)>v$, against the loss region $v<V_1^*$, weighted by how steep the profile is at each level: a wave invades ($c>0$) only if the threshold is low enough relative to the dispersal shape. Existence follows from monotone-operator theory for bistable integro-difference equations. Because of the Allee-type threshold, a release must exceed a *critical bubble* (a minimal infected region) to trigger the wave; fat-tailed kernels such as the Cauchy kernel change both the speed and the critical release size.

## Sources

- Z. Qu, T. Wu, E. Kwessi, "Travelling waves in Wolbachia spread dynamics", arXiv preprint (2026), Theorem 2.1, Theorem 3.4, Theorem 3.5, Proposition 4.1, <https://doi.org/10.48550/arXiv.2601.17590>.
