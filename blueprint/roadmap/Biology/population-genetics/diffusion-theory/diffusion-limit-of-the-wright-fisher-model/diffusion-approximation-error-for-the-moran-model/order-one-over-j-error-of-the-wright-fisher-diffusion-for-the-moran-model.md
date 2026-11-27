# Order-1/J error of the Wright–Fisher diffusion approximation of the Moran model

**Model.** A population of $J$ individuals of two types evolves in discrete steps: at each step one individual dies and is replaced, with probability $m$, by an immigrant from an infinite pool containing a fraction $p \in (0,1)$ of type 1, and otherwise by the offspring of a resident chosen with selective weight $1+s$ for type 1. The type-1 frequency $X^J_n \in I_J = \{0, 1/J, \dots, 1\}$ is a Markov chain with

$$\mathbb{P}\big(X^J_{n+1} = x + \tfrac1J \mid X^J_n = x\big) = (1-x)\Big(mp + (1-m)\frac{x(1+s)}{1+xs}\Big),$$

$$\mathbb{P}\big(X^J_{n+1} = x - \tfrac1J \mid X^J_n = x\big) = x\Big(m(1-p) + (1-m)\Big(1 - \frac{x(1+s)}{1+xs}\Big)\Big).$$

Under **weak selection and immigration**, $s = s'/J$ and $m = m'/J$ with $s' \in \mathbb{R}$, $m' \ge 0$. The approximating Wright–Fisher diffusion $Y^J$ has generator

$$L = \frac{1}{J^2}\,x(1-x)\frac{\partial^2}{\partial x^2} + \frac{1}{J}\big[s\,x(1-x) + m(p-x)\big]\frac{\partial}{\partial x},$$

so that $Z_t = Y^J_{J^2 t}$ solves $dZ_t = \sqrt{2Z_t(1-Z_t)}\,dB_t + [s'Z_t(1-Z_t) + m'(p-Z_t)]\,dt$, independent of $J$. Write $\|g\|_J = \max_{x\in I_J}|g(x)|$.

**Theorem.** Let $f \in C^4([0,1])$. There are constants $a, b > 0$ depending on $s'$ and $m'$ such that, for $J$ large,

$$\Big\|\mathbb{E}_x[f(X^J_n)] - \mathbb{E}_x[f(Y^J_n)]\Big\|_J \le \big(\|f'\|_J + \|f''\|_J\big)\,\frac{a\,e^{bn}}{J} + o\Big(\frac1J\Big).$$

If moreover $m' > |s'|$ (immigration dominates selection), there is $a > 0$ with

$$\Big\|\mathbb{E}_x[f(X^J_n)] - \mathbb{E}_x[f(Y^J_n)]\Big\|_J \le \big(\|f'\|_J + \|f''\|_J\big)\,\frac{a\,n}{J} + o\Big(\frac1J\Big),$$

so the error grows linearly rather than exponentially in time.

Hence, for a fixed time horizon, the diffusion approximation of the Moran model with weak selection and immigration has error $O(1/J)$ for $C^4$ test functions.

**Random environments.** The same order holds when the selection coefficient is itself random. If $s$ is a Markov chain on a finite set whose transition matrix satisfies $J^2 P \approx \alpha Q$ (limit a pure-jump process), and the limiting semigroup $(T_t)$ of the joint frequency–environment process satisfies $T_tf(\cdot,s) \in C^2(I)$ for every $s$ and every $f \in C^2(I)$ (Theorem 2), the error is at most $\tilde\Gamma(n)\,(\|f'\|_J + \|f''\|_J)/J + k_0(n)\max_{s,s'}|J^2P_{s,s'} - \alpha_s Q_{s,s'}|\,\|f\|_J + O(1/J^2)$ with $\tilde\Gamma$ at most exponential and $k_0$ linear in time. If the selection coefficient is $h(S_t)$, of order $1/J$, where $h$ is $C^2$ with values in a closed bounded interval contained in $(-1+\varepsilon,\infty)$ and the selection process has a diffusion limit $S_t$ (Section 5, Theorem 3), the joint error $\sup_x|\mathbb{E}_{x,s}f(X_n,Z_n) - \mathbb{E}_{x,s}f(Y_t,S_t)|$ is at most $q'(n)(\|\nabla f\| + \|\mathrm{Hess} f\|)/J + O(1/J^2)$ with $q'$ at most exponential in time.

## Depends on

- [Generator of the Wright–Fisher diffusion with selection and mutation](../../wright-fisher-diffusion-with-selection-and-mutat/selection-mutation-generator.md)

## Expansion

Let $S_1$ be the one-step transition operator of the chain and $T_t$ the diffusion semigroup. A Taylor expansion of $f(x \pm 1/J)$ shows that the one-step generator mismatch is $\|(S_1 - T_1)f\|_J \le C_1 J^{-3}\|f'\|_J + C_2 J^{-3}\|f''\|_J + O(J^{-4})$. The telescoping identity $S_n - T_n = \sum_{k} S_{n-k-1}(S_1 - T_1)T_k$ sums $n = O(J^2)$ such errors, so it suffices to control derivatives of $\phi(t,x) = T_t f(x)$. Differentiating the Kolmogorov equation gives a Feynman–Kac type equation for $\phi^{(j)}$ with killing rate $\nu_j(x) = j(j-1)/J^2 - j\,(s(1-2x) - m)/J$; this yields $\|\phi^{(j)}\| \le e^{c_j t/J^2}\sum_k a_{k,j}\|f^{(k)}\|$, the exponential factor. When $m' > |s'|$, immigration makes $\nu_1$ positive and the derivative bounds uniform in time, leaving only the linear growth from summing the steps. An appendix gives the analogous $O(1/J)$ bound for the Wright–Fisher chain, which needs $f \in C^5$ and $\|f'''\|_J$ as well.

## Sources

- Gorgui Gackou, Arnaud Guillin and Arnaud Personne, "Quantitative approximation of the discrete Moran process by a Wright–Fisher diffusion", *J. Math. Biol.* 81(2) (2020), 575–602. <https://doi.org/10.1007/s00285-020-01520-y>
- Preprint version (the locators in this item follow its numbering): Gorgui Gackou, Arnaud Guillin and Arnaud Personne, "When can the discrete Moran process be replaced by Wright–Fisher diffusion?", arXiv:1905.04040 (2019), Section 2 (model), Theorem 1 with Lemmas 1–2 and Proposition 1 (Section 3), Theorem 2 (Section 4), Theorem 3 (Section 5) and Theorem 4 (Section 6), <https://doi.org/10.48550/arXiv.1905.04040>.
