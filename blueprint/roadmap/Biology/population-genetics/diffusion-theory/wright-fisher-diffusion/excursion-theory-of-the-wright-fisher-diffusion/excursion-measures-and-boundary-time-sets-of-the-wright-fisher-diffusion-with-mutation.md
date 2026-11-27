# Excursion measures and boundary time sets of the Wright–Fisher diffusion with mutation

**Setting.** $X$ is the Wright-Fisher diffusion on $[0,1]$ with generator

$$\mathscr{G}=\tfrac12x(1-x)\frac{d^2}{dx^2}+\tfrac12(\theta_1-|\theta|x)\frac{d}{dx},\qquad |\theta|=\theta_1+\theta_2,$$

with $0<\theta_1,\theta_2<1$, so both endpoints are regular and the stationary law is Beta$(\theta_1,\theta_2)$. Let $H_0,H_1$ be hitting times of $0$ and $1$. The *killed* diffusion is sent to a cemetery at $H_0\wedge H_1$. For a boundary point $y$ and $b\in\{0,1\}$, the excursions of $X$ that start at $y$ and are killed on reaching $b$ form the excursion process $\Xi^{y\to b}$ indexed by local time at $y$. Throughout, the speed measure is normalized as the Beta$(\theta_1,\theta_2)$ law, $m(dx)=x^{\theta_1-1}(1-x)^{\theta_2-1}dx/B(\theta_1,\theta_2)$, and local time is the Itô–McKean local time with respect to $m$: $\int_0^t g(X_u)\,du=\int g(y)\,L^y_t\,m(dy)$ for nonnegative Borel $g$. Replacing $m$ by $cm$ divides local time by $c$ and multiplies the excursion measures, and the limit in statement 2, by $c$. Write $a(\lambda),b(\lambda)=\tfrac12\big(|\theta|-1\pm\sqrt{(|\theta|-1)^2-8\lambda}\big)$ and ${}_2F_1$ for the Gauss hypergeometric function.

**Statements.**
1. *(Resolvent and Green function.)* The Green function of $X$, i.e. the $\lambda$-potential density $G_\lambda(x,y)$ with respect to $m(dy)$ (so $\mathbb E_x\int_0^\infty e^{-\lambda t}g(X_t)\,dt=\int G_\lambda(x,y)g(y)\,m(dy)$), has the three forms: a Jacobi-polynomial eigen-expansion $\sum_n\frac{2}{2\lambda+n(n+|\theta|-1)}\pi_n^{-1}R_n(x)R_n(y)$; a mixture over the block-counting (line-of-descent) representation; and the Wronskian form

$$G_\lambda(x,y)=\frac{2\Gamma(a(\lambda))\Gamma(b(\lambda))}{\Gamma(|\theta|)}\,{}_2F_1\big(a,b;\theta_1;x\wedge y\big)\,{}_2F_1\big(a,b;\theta_2;1-(x\vee y)\big).$$

The resolvent of the twice-killed process is given explicitly by subtracting boundary terms built from the four fundamental solutions ${}_2F_1(a,b;\theta_2;1-x)$, $x^{1-\theta_1}{}_2F_1(\theta_2-b,\theta_2-a;2-\theta_1;x)$, $(1-x)^{1-\theta_2}{}_2F_1(\theta_1-a,\theta_1-b;2-\theta_2;1-x)$, ${}_2F_1(a,b;\theta_1;x)$.
2. *(Poisson structure.)* $\Xi^{y\to b}$ is a Poisson point process with intensity $\mathrm{Leb}\otimes n^{y\to b}$ for a $\sigma$-finite excursion measure $n^{y\to b}$, whose finite-dimensional marginals are an entrance law followed by killed transition kernels. The $\lambda$-potentials $n^{0\to1}_\lambda(dx)$, $n^{1\to0}_\lambda(dx)$ have explicit densities proportional to $x^{\theta_1-1}(1-x)^{\theta_2-1}$ times combinations of ${}_2F_1$ functions, and

$$\lim_{\lambda\to0}\lambda\,n^{0\to1}_\lambda1=\lim_{\lambda\to0}\lambda\,n^{1\to0}_\lambda1=\frac{1}{2B(\theta_1,\theta_2)B(1-\theta_1,1-\theta_2)} .$$

Concatenating marked excursions reconstructs the Wright-Fisher path.
3. *(Boundary time sets.)* For fixed $T>0$, the closure $\mathcal{R}_0$ of $\{t:X_t=0\}$ satisfies $\dim_H(\mathcal{R}_0\cap[0,T])=1-\theta_1$ almost surely under $\mathbb{P}_0$, and $\dim_H(\mathcal{R}_1\cap[0,T])=1-\theta_2$ under $\mathbb{P}_1$.
4. *(Singularity.)* For distinct $(\theta_1,\theta_2)\ne(\theta_1',\theta_2')$ in $(0,1)^2$, the path laws up to any fixed $T>0$ are mutually singular: the mutation rates can be read off a single path.

## Depends on

- [Absorption time of the Wright-Fisher diffusion](../../fixation-and-absorption-in-the-wright-fisher-dif/absorption-time.md)

## Expansion

The hypergeometric equation $\mathscr{G}u=\lambda u$ has exponents $0$ and $1-\theta_1$ at $0$ and $0$ and $1-\theta_2$ at $1$, so the four Kummer solutions above are the increasing/decreasing and boundary-regular/singular solutions; the Green function is their normalized product, and killing at the endpoints subtracts the boundary-hitting contributions. Excursion measures arise as limits $x\to y$ of the killed resolvent divided by the probability of exiting at the far boundary, giving the explicit formulas. Near $0$ the scale function behaves like $x^{1-\theta_1}$, so the inverse local time at $0$ is a stable subordinator of index $1-\theta_1$, whose range has Hausdorff dimension $1-\theta_1$; since this dimension is a path functional, different $\theta$ give singular laws.

## Sources

- Paul A. Jenkins, Jere Koskela, Victor M. Rivero, Jaromir Sant, Dario Spanò and Ivana Valentić, "Excursion theory for the Wright–Fisher diffusion", Electron. J. Probab. 30 (2025), 1–31, <https://doi.org/10.1214/25-EJP1354>. Numbering follows the arXiv version, arXiv:2309.16271 (2023): Propositions 2.1, 2.2, 3.1, 3.2, Theorem 3.1, Corollary 3.1, Theorems 4.1–4.4 and Corollaries 4.1–4.2, <https://doi.org/10.48550/arXiv.2309.16271>.
