# Uniqueness of the QSD when an absorbed diffusion comes down from infinity

**Setting.** Let $Z$ be the absorbed diffusion $dZ^i_t=b_i(Z_t)\,dt+\sqrt{a_i(Z^i_t)}\,dW^i_t$ on $[0,\infty)^d$ satisfying (H1)–(H3) of the existence theorem, with QSD $\mu_1$ and sharp rate $r_1>0$. Assume in addition

(H4) there are $C,\gamma,R_*>0$ with

$$\lim_{|z|\to\infty}V^{-\gamma-2}\sum_{i}a_i|\partial_{z_i}V|^2=0,\qquad \tfrac12\sum_i a_i\,\partial^2_{z_iz_i}V+b\cdot\nabla V\le -C\,V^{\gamma+1}\quad\text{outside } B^+_{R_*}.$$

(H4) implies that $Z$ **comes down from infinity**: for each $\lambda>0$ there is $R$ with $\sup_{z}\mathbb{E}^z[e^{\lambda T_R}]<\infty$, where $T_R$ is the entrance time into the box $B^+_R$.

**Theorem.** Under (H1)–(H4), $\mu_1$ is the unique QSD of $Z$, and for every initial law $\mu$ on $(0,\infty)^d$ (no compact support needed), every $f\in C_b$ and small $\varepsilon>0$,

$$\lim_{t\to\infty}e^{(r_1-\varepsilon)t}\Big|\mathbb{E}^\mu\big[f(Z_t)\mid t<T_\Gamma\big]-\int f\,d\mu_1\Big|=0 .$$

This applies to stochastic Lotka–Volterra competition $dZ^i=Z^i(r_i-\sum_jc_{ij}Z^j)\,dt+\sqrt{\gamma_iZ^i}\,dW^i$ with $c_{ij}>0$, and to weakly cooperative systems where the off-diagonal $-c_{ij}$ are positive but small relative to $c_{ii}$.

## Depends on

- [Existence and sharp exponential convergence to a QSD of multidimensional absorbed diffusions](existence-and-sharp-exponential-convergence-to-a-qsd-of-multidimensional-absorbed-diffusions.md)

## Expansion

Strong dissipativity at infinity makes the process enter a fixed bounded box in a time with exponential moments of every order. Hence the mass of any initial law, however heavy-tailed, is transported into a compact region before conditioning matters, and the compact-support convergence of the existence theorem extends to all initial laws. Any QSD is then a fixed point attracted to $\mu_1$, so it equals $\mu_1$.

## Sources

- Alexandru Hening, Weiwei Qi, Zhongwei Shen and Yingfei Yi, "Quasi-stationary distributions of multi-dimensional diffusion processes", arXiv:2102.05785 (2021), Theorem B, assumption (H4) and Section 6 (applications), <https://doi.org/10.48550/arXiv.2102.05785>.
