# Existence and sharp exponential convergence to a QSD of multidimensional absorbed diffusions

**Model.** On $\overline{U}=[0,\infty)^d$ consider

$$dZ^i_t=b_i(Z_t)\,dt+\sqrt{a_i(Z^i_t)}\,dW^i_t,\qquad i=1,\dots,d,$$

with independent Brownian motions $W^i$, absorbed at the extinction set $\Gamma=\{z\in\overline U: z_i=0\text{ for some } i\}$, $T_\Gamma=\inf\{t>0:Z_t\in\Gamma\}$. A typical case is the stochastic Lotka–Volterra community $dZ^i=Z^i(r_i-\sum_j c_{ij}Z^j)\,dt+\sqrt{\gamma_iZ^i}\,dW^i$. A probability measure $\mu$ on $U=(0,\infty)^d$ is a **quasi-stationary distribution (QSD)** if $\mathbb{P}^\mu[Z_t\in\cdot\mid t<T_\Gamma]=\mu$ for all $t\ge 0$.

**Hypotheses.** (H1) $a_i\in C^2([0,\infty))$, $a_i(0)=0<a_i'(0)$, $a_i>0$ on $(0,\infty)$, $\limsup_{s\to\infty}\big(|a_i'|^2/a_i+a_i''\big)<\infty$ and $\int_1^\infty a_i^{-1/2}\,ds=\infty$. (H2) $b_i\in C^1(\overline U)$ with $b_i=0$ on $\{z_i=0\}$. (H3) There is a positive $V\in C^2(\overline U)$ such that:
- (1) $V(z)\to\infty$ and $(b\cdot\nabla V)(z)\to-\infty$ as $|z|\to\infty$;
- (2) there is a nonnegative continuous $\tilde V:[0,\infty)\to[0,\infty)$ with $\int_1^\infty e^{-\beta\tilde V(s)}a_i(s)^{-1}\,ds<\infty$ for all $\beta>0$ and all $i$, and $V(z)\ge\sum_{i=1}^d\tilde V(z_i)$ on $U$;
- (3) $\displaystyle\lim_{|z|\to\infty}\frac{1}{b\cdot\nabla V}\sum_{i=1}^d\Big(|\partial_{z_i}b_i|+\frac{|a_i'b_i|}{a_i}+|a_i'\partial_{z_i}V|+|a_i\partial^2_{z_iz_i}V|\Big)=0$;
- (4) there are $C,R>0$ with $\sum_{i=1}^d\big(a_i|\partial_{z_i}V|^2+b_i^2/a_i\big)\le-C\,b\cdot\nabla V$ on $U\setminus B^+_R$, where $B^+_R=(0,R)^d$.

**Theorem.** Under (H1)–(H3), $Z$ reaches $\Gamma$ in finite time almost surely, it admits a QSD $\mu_1$, and there is $r_1>0$ such that for every compactly supported initial law $\mu$ on $U$, every $f\in C_b(U)$ and every small $\varepsilon>0$,

$$\lim_{t\to\infty}e^{(r_1-\varepsilon)t}\Big|\mathbb{E}^\mu\big[f(Z_t)\mid t<T_\Gamma\big]-\int_U f\,d\mu_1\Big|=0 .$$

The rate is sharp: there is $f\in C_b(U)$ such that for a.e. $x\in U$ there is a family of sets $K_{x,\varepsilon}\subset(0,\infty)$, with $K_{x,\varepsilon_2}\subset K_{x,\varepsilon_1}$ for $0<\varepsilon_1<\varepsilon_2\ll1$ and $\lim_{\varepsilon\to0}\inf_{T>0}\big|K_{x,\varepsilon}\cap(T,T+1)\big|=1$, such that

$$\lim_{t\in K_{x,\varepsilon},\ t\to\infty}e^{(r_1+\varepsilon)t}\Big|\mathbb{E}^x\big[f(Z_t)\mid t<T_\Gamma\big]-\int_U f\,d\mu_1\Big|=\infty .$$

Here $r_1$ is the spectral gap between the principal eigenvalue $\lambda_1$ and the rest of the spectrum of the associated Fokker–Planck operator in a weighted space, $\mu_1$ is given by its positive principal eigenfunction, and $\lambda_1$ is the extinction rate: $\mathbb{P}^{\mu_1}[t<T_\Gamma]=e^{-\lambda_1t}$.

## Expansion

The change of variables $x_i=\xi_i(z_i)=\int^{z_i}a_i^{-1/2}$ gives unit diffusion, and conjugating the Fokker–Planck operator by $e^{Q/2+\beta U}$ produces a uniformly elliptic operator with singular coefficients only in its zeroth-order terms. For that operator one proves compact resolvent in a weighted Hilbert space, a simple dominant principal eigenvalue with an a.e. positive eigenfunction (Krein–Rutman type), an analytic, positive, immediately compact semigroup, and a stochastic representation of the semigroup in terms of the killed process. The spectral decomposition then yields the QSD and the exponential rate. Because the process is irreversible, the remaining spectrum can be complex, which is the source of the oscillations behind the sharpness statement.

## Sources

- Alexandru Hening, Weiwei Qi, Zhongwei Shen and Yingfei Yi, "Quasi-stationary distributions of multi-dimensional diffusion processes", J. Dyn. Differ. Equ. 38 (2026) 377–435, Theorem A; preprint arXiv:2102.05785 (2021), Theorem A, Proposition 2.1 and Sections 3–5, <https://doi.org/10.48550/arXiv.2102.05785>.
