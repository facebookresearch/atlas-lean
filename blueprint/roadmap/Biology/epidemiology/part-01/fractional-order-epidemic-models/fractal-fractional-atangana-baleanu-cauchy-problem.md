# Fractal-fractional Atangana–Baleanu Cauchy problem

Let $0<\alpha_1<1$ (fractional order) and $0<\alpha_2\le 1$ (fractal dimension), and set $AB(\alpha_1)=1-\alpha_1+\alpha_1/\Gamma(\alpha_1)$, so $AB(0)=AB(1)=1$.

**Atangana–Baleanu–Caputo derivative.** For $g$ in the Sobolev space $W^{1,2}$,

$$
{}^{ABC}_{\;\;0}D_t^{\alpha_1}g(t)=\frac{AB(\alpha_1)}{1-\alpha_1}\int_0^t g'(\tau)\,E_{\alpha_1}\!\Big[-\frac{\alpha_1}{1-\alpha_1}(t-\tau)^{\alpha_1}\Big]d\tau ,
$$

a non-singular Mittag-Leffler kernel in place of the Caputo power-law kernel.

**Fractal-fractional derivative.** Replacing $d/dt$ by the fractal derivative $\frac{dg}{dt^{\alpha_2}}=\lim_{s\to t}\frac{g(t)-g(s)}{t^{\alpha_2}-s^{\alpha_2}}$ gives the fractal-fractional operator ${}^{FFM}D^{\alpha_1,\alpha_2}_{0,t}$ with Mittag-Leffler kernel, whose associated integral is

$$
{}^{FFM}J^{\alpha_1,\alpha_2}_{0,t}g(t)=\frac{\alpha_1\alpha_2}{AB(\alpha_1)\Gamma(\alpha_1)}\int_0^t s^{\alpha_2-1}g(s)(t-s)^{\alpha_1-1}ds+\frac{\alpha_2(1-\alpha_1)}{AB(\alpha_1)}t^{\alpha_2-1}g(t).
$$

**Integral form of the epidemic Cauchy problem.** A compartmental model ${}^{FFM}D^{\alpha_1,\alpha_2}_{0,t}x(t)=g(t,x(t))$, $x(0)=x_0$, is turned into an integral equation by integrating: every solution of the Cauchy problem satisfies

$$
x(t)=x_0+\frac{1-\alpha_1}{AB(\alpha_1)}\,\alpha_2 t^{\alpha_2-1}g(t,x(t))+\frac{\alpha_1\alpha_2}{AB(\alpha_1)\Gamma(\alpha_1)}\int_0^t \tau^{\alpha_2-1}g(\tau,x(\tau))(t-\tau)^{\alpha_1-1}d\tau .
$$

The converse is not claimed: for $\alpha_2=1$ the ABC derivative of a $W^{1,2}$ function tends to $0$ as $t\to0$, so a solution of the Cauchy problem needs $g(0,x_0)=0$, while the integral equation has continuous solutions with $g(0,x(0))\ne0$.

The source applies this to an eight-compartment COVID-19 model $(S,E,I,A,Q,H,R,M)$ with force of infection $\lambda=\eta_1(I+\psi A)/N+\eta_2 M$, in which each integer-order derivative is replaced by ${}^{FFM}D^{\alpha_1,\alpha_2}_{0,t}$; at $\alpha_1=\alpha_2=1$ the integral form reduces to the classical $x(t)=x_0+\int_0^t g(\tau,x(\tau))\,d\tau$.

## Depends on

- [Well-posedness of Caputo fractional initial value problems](caputo-fractional-initial-value-problem-well-posedness.md)

## Expansion

By the chain rule for the fractal derivative, $\frac{dg}{dt^{\alpha_2}}=\frac{g'(t)}{\alpha_2 t^{\alpha_2-1}}$, so the fractal-fractional problem is equivalent to the ABC problem ${}^{ABC}_{\;\;0}D_t^{\alpha_1}x=K(t,x)$ with $K(t,x)=\alpha_2t^{\alpha_2-1}g(t,x)$. Applying the Atangana–Baleanu integral $\frac{1-\alpha_1}{AB(\alpha_1)}K+\frac{\alpha_1}{AB(\alpha_1)\Gamma(\alpha_1)}\int_0^t K(\tau)(t-\tau)^{\alpha_1-1}d\tau$ yields the displayed equation; the source discretizes it with a three-point Newton interpolation of $K$ on each subinterval. For $\alpha_2=1$ (the ABC problem with normalization $B(\alpha_1)$ in place of $AB(\alpha_1)$), Picard iterates of the integral equation converge to a unique solution on $[0,b]$ when $\frac{1-\alpha_1}{B(\alpha_1)}\eta_i+\frac{b^{\alpha_1}}{B(\alpha_1)\Gamma(\alpha_1)}\eta_i<1$ for the Lipschitz constants $\eta_i$ of the right-hand sides, and the solution is Hyers–Ulam stable (Li et al., Theorems 3–4).

## Sources

- M. A. Khan, A. Atangana, E. Alzahrani, Fatmawati, "The dynamics of COVID-19 with quarantined and isolation", *Advances in Difference Equations* 2020 (2020) 425. <https://doi.org/10.1186/s13662-020-02882-9>. PMCID: PMC7427274. (Definitions 1–2, model (7), Eqs. (15)–(17).)
- A. Atangana, D. Baleanu, "New fractional derivatives with nonlocal and non-singular kernel: theory and application to heat transfer model", *Thermal Science* 20 (2016) 763–769. <https://doi.org/10.2298/TSCI160111018A>
- A. Atangana, "Fractal-fractional differentiation and integration: connecting fractal calculus and fractional calculus to predict complex system", *Chaos, Solitons & Fractals* 102 (2017) 396–406. <https://doi.org/10.1016/j.chaos.2017.04.027>
- X.-P. Li, H. A. Bayatti, A. Din, A. Zeb, "A vigorous study of fractional order COVID-19 model via ABC derivatives", Results in Physics (2021), Theorem 3 (existence and uniqueness, Eq. 20) and Theorem 4 (Hyers–Ulam stability), <https://doi.org/10.1016/j.rinp.2021.104737> (PMC8401151).
