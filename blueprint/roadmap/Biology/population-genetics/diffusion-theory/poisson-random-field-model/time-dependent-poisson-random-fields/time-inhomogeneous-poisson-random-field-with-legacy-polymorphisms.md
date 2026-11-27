# Time-inhomogeneous Poisson random field with legacy polymorphisms

**Setting.** At each site the number of mutant nucleotides in a haploid population of size $N$ follows Moran's model, with mutant fitness $1+\sigma_N$, no repeat mutation at a site, and traps at $0$ and $N$. At time $0$ the counts $N_0(i)$ of sites with $i$ mutant copies are independent Poisson with means $\omega^N_i$; each later step brings a Poisson($\mu_N$) number of new mutations at new sites, each starting at one copy. Let $N_k(j)$ be the number of sites carrying $j$ mutant copies at step $k$. Assume

$$
N\sigma_N\to\gamma,\qquad N\mu_N\to\theta,\qquad k_N/N^2\to t,
$$

and that $\sum_j g(j/N)(j/N)\,\omega^N_j\to\int_0^1 g(y)\,y\,\nu(dy)$ for all $g\in C[0,1]$, for a Borel measure $\nu$ on $(0,1)$ with $\int_0^1 x\,\nu(dx)<\infty$ (the ancestral, or legacy, polymorphisms).

Let $X_t$ be the limiting diffusion with generator $x(1-x)\frac{d^2}{dx^2}+\gamma x(1-x)\frac{d}{dx}$, scale function $s(x)=(1-e^{-\gamma x})/\gamma$, speed measure $m(dx)=e^{\gamma x}\,dx/(x(1-x))$, symmetric transition density $p(t,x,y)$ with respect to $m$, and $Q_tf(x)=\int_0^1 p(t,x,y)f(y)\,m(dy)$.

**Theorem (polymorphic sites).** For every $f\in C[0,1]$ with $f(0)=f(1)=0$ such that $f(x)/x$ extends continuously to $[0,1]$,

$$
\lim_{N\to\infty}\mathbb{E}\sum_{i=1}^{N-1}f\big(\tfrac iN\big)N_{k_N}(i)=\int_0^1Q_tf(x)\,\nu(dx)+\theta\int_0^1\frac{s(1)-s(x)}{s(1)-s(0)}\big(f(x)-Q_tf(x)\big)\,m(dx).
$$

Since the counts are independent Poisson for each $k$, the polymorphic frequencies converge to a Poisson random field on $(0,1)$ whose mean density with respect to $m(dy)$ is

$$
g(t,y)=\int_0^1p(t,x,y)\,\nu(dx)+\theta\,\frac{s(1)-s(y)}{s(1)}-\theta\int_0^1\frac{s(1)-s(x)}{s(1)}\,p(t,x,y)\,m(dx).
$$

The first term is the legacy contribution and the rest comes from mutations arising after time $0$.

**Corollary (approach to equilibrium).** As $t\to\infty$ the right-hand side converges to $\int_0^1 f\,d\mu_{\theta,\gamma}$, where

$$
\mu_{\theta,\gamma}(dx)=\theta\,\frac{s(1)-s(x)}{s(1)}\,m(dx)=\frac{s(1)-s(x)}{x(1-x)}\,\frac{\theta e^{\gamma x}}{s(1)}\,dx,
$$

the equilibrium Poisson random field; taking $\nu=\mu_{\theta,\gamma}$ makes the right-hand side constant in $t$.

**Theorem (fixations).** The number of sites fixed for the mutant nucleotide by time $t$ is asymptotically Poisson, independent of the polymorphic field, with mean

$$
\int_0^1P_x(T_1\le t)\,\nu(dx)+\frac{\theta}{s(1)}\int_0^t\widetilde P_0(T_1\le u)\,du,
$$

where $T_a$ is the hitting time of $a$ and $\widetilde P$ is the law of $X$ conditioned on $T_1<T_0$, which has an entrance boundary at $0$.

## Depends on

- [Sawyer–Hartl Poisson random field density](../prf-density.md)

## Expansion

By the Moran-to-diffusion limit on time scale $k\sim tN^2$, a legacy site starting at frequency $x$ is at frequency $y$ at time $t$ with density $p(t,x,y)$, giving $\int Q_tf\,d\nu$. New mutations arrive at rate $N^2\mu_N\approx N\theta$ but start at $1/N$, and only a fraction $s(1/N)/s(1)\approx 1/(N s(1))$ escape loss, so $O(\theta)$ survive per unit time. Integrating the surviving mutations over arrival times $u\in[0,t]$, and using $\int_0^\infty p(u,x,y)\,du$ for the Green function together with symmetry of $p$, gives the equilibrium density minus its time-$t$ transport, which is the second term. Fixations arise from legacy sites hitting $1$ and from new mutants that, conditioned to fix, enter from $0$ under $\widetilde P$.

## Sources

- Amei Amei and Stanley Sawyer, *A time-dependent Poisson random field model for polymorphism within and between two related biological species*, Annals of Applied Probability 20 (2010), 1663–1696, <https://doi.org/10.1214/09-AAP668>; arXiv:1011.1724, Theorem 2.1, Corollary 2.1, Theorem 2.2 and equations (2.10), (2.14). <https://doi.org/10.48550/arXiv.1011.1724>
