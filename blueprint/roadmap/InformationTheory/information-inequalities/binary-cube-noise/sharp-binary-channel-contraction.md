# Sharp contraction and entropy production for binary channels on the cube

On $\{0,1\}^n$ ($n\ge0$), write $\mathbb E$ for the uniform average and set $L=\log2$, $\psi(a)=\tfrac12(1+a)\log(1+a)+\tfrac12(1-a)\log(1-a)$ with $0\log0=0$, and $H(a)=L-\psi(a)$. The inverse $\psi^{-1}$ is taken on $[0,1]$. Given $u:\{0,1\}^n\to[-1,1]$, let $I(u)=H(\mathbb E u)-\mathbb E H(u)$. For $\rho\in[-1,1]$, $T_\rho u(y)$ is the average of $u(x)$ when coordinates of $x$ independently agree with $y$ with probability $(1+\rho)/2$.

* $I(T_\rho u)\le\psi(|\rho|\psi^{-1}(I(u)))$. Equality holds for every $u(x)=a(2x_i-1)$ with $|a|\le1$ and every coordinate $i$.
* If input $X$ is uniform, the binary output $B$ has conditional probability $(1+u(X))/2$ of being $1$, and $Y$ is independently obtained from $X$ by correlation-$\rho$ noise given $X$, the mutual information $I(B;Y)$ in nats is exactly $I(T_\rho u)$.
* For Boolean $f$, put $m=\mathbb E(2f-1)$ and $b=\psi(|\rho|\psi^{-1}(H(m)))$. The mutual information $I(f(X);Y)$ equals $I(T_\rho(2f-1))$, is at most $b$, and $b\le\psi(|\rho|)$, strictly if $0<|m|<1$ and $0<|\rho|$. Every coordinate and its complement give information $\psi(|\rho|)$. For $0\le\varepsilon\le1/2$ one has $\psi(1-2\varepsilon)/L=1-h_2(\varepsilon)$ and at crossover $\varepsilon$ the mutual information in bits is at most that value. Here $h_2(t)=-[t\log t+(1-t)\log(1-t)]/L$.
* For $g$ taking values strictly in $(-1,1)$ let $Dg(x)=\tfrac12\sum_i(g(x)-g(x^{\oplus i}))$, where $x^{\oplus i}$ flips coordinate $i$. Write $F(s)=\psi^{-1}(s)\operatorname{artanh}(\psi^{-1}(s))$ for $0\le s<L$, with $S(s)=0$ for $s<0$ and $S(s)=F(s)-2s$ otherwise on $s<L$. For $m=\mathbb E g$, $v=I(g)$, put $R=2v+(1-m^2)S(L-(H(m)-v)/(1-m^2))$. Then $F(v)\le\max\{R,F(v)\}\le\mathbb E[\operatorname{artanh}(g)Dg]$. This clause does not prescribe a finite value $F(L)$.

**Conventions.** Use finite binary joint laws and mutual information in nats, together with the product noise operator in the sign convention above and the inverse of $\psi$ on the nonnegative branch.

## Depends on

- [Binary-cube bit noise and the sign-convention noise operator](bernoulli-cube-noise.md)

## Proof depends on

Sharp mean-dependent entropy production, its integration along the cube noise semigroup, and the identification of the noisy conditional bit mean with $T_\rho u$.

## Expansion

Separate the generator estimate, semigroup contraction, nats identity, soft-coordinate equality, bias refinement, Boolean equality and bits conversion. Prove the closed-interval estimate by approximation from interior inputs and use reflection for negative $\rho$. The stronger generator estimate and its endpoint passage are mathematical prerequisites, not additional assumptions on the channel.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SoftChannel204.lean#L114-L116)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/119.md)
- [Accompanying manuscript: Sharp binary-information contraction on the discrete cube](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Sharp-binary-information-contraction-on-the-discrete-cube-September-24-2026/main.pdf)
- [Background: Courtade and Kumar, *Which Boolean Functions Maximize Mutual Information on Noisy Inputs?* (2014)](https://doi.org/10.1109/TIT.2014.2326877)
