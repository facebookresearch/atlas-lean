# Superexponential mutant growth under unbounded random fitness increments

**Model.** As in the bounded case: type-0 cells grow deterministically as $V_0e^{\lambda_0t}$ ($\lambda_0>0$), each type-0 cell produces type-1 mutants at rate $u_1$, and a mutant's birth rate exceeds the type-0 birth rate by an independent random increment $X$; each mutant founds a birth–death branching process, and $Z_1(t)$ counts type-1 cells. Now $X$ has an unbounded generalized Fréchet-type tail

$$\Pr(X>x)=x^{\beta}e^{-\gamma x^{\alpha}},\qquad \gamma,\alpha>0,\ \beta\in\mathbb R,$$

which covers gamma laws ($\alpha=1$) and, asymptotically, Gaussian increments ($\alpha=2$, $\beta=-1$).

**Theorem (exponential-type tail, $\alpha=1$).** Let $c_0=\lambda_0/(4\gamma)$. Then $t^{-2}\log Z_1(t)\to c_0$, and

$$\frac1t\Big[\log Z_1(t)-c_0t^2\Big(1+\frac{(2\beta+1)\log t}{\lambda_0t}\Big)\Big]\Rightarrow y^*,$$

where $y^*$ is the rightmost point of a Poisson process with intensity

$$(2c_0)^{\beta}\,(\pi/\lambda_0)^{1/2}\,V_0u_1\,\exp\!\big(\gamma\lambda_0-\lambda_0y/(2c_0)\big).$$

**Theorem (integer $\alpha>1$).** There are explicit constants $c_k=c_k(\alpha,\gamma)$, $0\le k<\alpha$, and $\kappa=\kappa(\beta,\alpha,\gamma)$ such that $t^{-(\alpha+1)/\alpha}\log Z_1(t)\to c_0$ and

$$\frac{1}{t^{1/\alpha}}\Big[\log Z_1(t)-c_0t^{(\alpha+1)/\alpha}\Big(1+\sum_{1\le k<\alpha}c_kt^{-k/\alpha}+\kappa\frac{\log t}{t}\Big)\Big]\Rightarrow y^*,$$

with $y^*$ the rightmost particle of a point process with explicit intensity.

So $\log Z_1(t)$ grows like $t^{(\alpha+1)/\alpha}$ rather than linearly, and, unlike the bounded case, the type-1 population is dominated by the descendants of a single mutant: the one with the largest growth exponent, born at time $s\approx t/(\alpha+1)$ with increment of order $t^{1/\alpha}$.

**Conjecture (stated, not proved).** With $q(k)=\sum_{j=0}^{k}\alpha^{-j}$, $t^{-q(k)}\log Z_k(t)\to c_k$; for exponential tails $q(k)=k+1$.

## Expansion

A mutant born at time $s$ with increment $x$ that survives reaches size about $\zeta e^{(\lambda_0+x)(t-s)}$ with $\zeta$ exponential, so $\log Z_1(t)$ is governed by the maximum of the growth exponents $z=(\lambda_0+x)(t-s)$ over the Poisson process of mutations. The expected number of mutations with exponent at least $z$ is

$$\mu(z,\infty)=V_0u_1\int_0^t\Big(\frac{z}{t-s}-\lambda_0\Big)^{\beta}\exp\big(\phi(s,z)\big)\,ds,\qquad \phi(s,z)=\lambda_0s-\gamma\Big(\frac{z}{t-s}-\lambda_0\Big)^{\alpha},$$

and $\phi(\cdot,z)$ is concave in the relevant range, so Laplace's method locates the maximizing birth time $s_z$. For $\alpha=1$ the maximizer is explicit, which gives the $t^2$ leading order with constant $\lambda_0/(4\gamma)$ and the Gumbel-type fluctuations of order $t$; for $\alpha>1$ the fluctuations are only of order $t^{1/\alpha}$, which forces the finer expansion of the centering. The extreme point dominates the sum because the intensity decays exponentially in $y$.

These are Theorems 6 and 7 and Conjecture 1 of the source.

## Depends on

- [Growth of mutant generations under bounded random fitness increments](growth-of-mutant-generations-under-bounded-random-fitness-increments.md)

## Sources

- R. Durrett, J. Foo, K. Leder, J. Mayberry, F. Michor, *Evolutionary dynamics of tumor progression with random fitness values*, Theoretical Population Biology 78 (2010); arXiv:1003.1927. <https://doi.org/10.48550/arXiv.1003.1927>
