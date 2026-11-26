# Central limit theorem for the driver site frequency spectrum

**Model.** A two-type continuous-time linear birth–death process: type-0 (wild-type) cells divide at rate $a$ and die at rate $d$; at each type-0 division one offspring is a type-1 (driver) cell with probability $v$, and each type-0 cell also mutates to type-1 at rate $\mu$. Type-1 cells divide at rate $a+b$ ($b>0$) and die at rate $d$. The net growth rates are $\lambda_0 = a(1-v)-d-\mu>0$ and $\lambda_1 = a+b-d$. Let $P_j(t)$ be the probability that a type-1 clone started from one cell has size $j$ at age $t$, and let $S_j(t)$ (the *driver site frequency spectrum*) be the number of type-1 clones of size $j$ at time $t$. On the survival event $\Omega_0^\infty$ of the type-0 population, $e^{-\lambda_0 t}Z_0(t)\to Y$ almost surely, and $Y$ is exponential; $W=\lim_t e^{-\lambda_1 t}Z(t)$, and $\tau_n$ is the first time the total population reaches $n$.

**Theorem (second-order fluctuations).** Let
$$X_{t,j} = e^{-\lambda_0 t/2}\Big(S_j(t) - (av+\mu)\,Y\int_0^t P_j(t-s)\,e^{\lambda_0 s}\,ds\Big).$$
Conditionally on $\Omega_0^\infty$, $(X_{t,j})_{j\ge1}$ converges stably (with respect to the full clone history) in $\ell^p$, $p\in[2,\infty]$, to a limit $(X_{\infty,j})_{j\ge1}$ which, given $Y$, is a mean-zero Gaussian process independent of that history with covariance $\mathbb{E}[X_{\infty,j}X_{\infty,k}\mid Y] = Y\sigma_{j,k}$ for explicit constants $\sigma_{j,k}$ that decay like $(jk)^{-1}(j+k)^{-\lambda_0/\lambda_1}$ for $j\ne k$. At detection sizes,
$$n^{-\lambda_0/(2\lambda_1)}\Big(S_j(\tau_n) - (av+\mu)\,Y\int_0^{\tau_n} P_j(\tau_n-s)\,e^{\lambda_0 s}\,ds\Big)_{j\ge1} \Rightarrow W^{-\lambda_0/(2\lambda_1)}\,(X_{\infty,j})_{j\ge1}$$
stably in $\ell^p$ for $p$ large enough. Almost surely, $\limsup_{j}X_{\infty,j}/\sqrt{2Y\sigma_{j,j}\log j}=1$ and the corresponding $\liminf$ is $-1$.

## Expansion

Driver clones are founded at the times of a Cox process with intensity $(av+\mu)Z_0(s)\approx(av+\mu)Ye^{\lambda_0 s}$, and each grows independently; the centring term is the conditional mean given the type-0 path. Conditioning on the early history and applying a martingale central limit theorem to the independent clone contributions gives Gaussian fluctuations of order $e^{\lambda_0 t/2}$, whose variance is proportional to the number of clones and hence to $Y$. Using $\tau_n\approx\lambda_1^{-1}\log(n/W)$ converts the time scaling into the size scaling. The result yields confidence intervals for consistent estimators of the selective advantage $b$.

## Sources

- A. Ahmed, J. Foo, K. Leder, "A central limit theorem for the driver site frequency spectrum", arXiv:2610.32942, Section 2 (model) and Section 3 (central limit theorems at large times and at detection sizes). <https://doi.org/10.48550/arXiv.2610.32942>
