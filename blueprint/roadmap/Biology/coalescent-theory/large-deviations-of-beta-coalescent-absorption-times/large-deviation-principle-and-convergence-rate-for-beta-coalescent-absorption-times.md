# Large deviation principle and convergence rate for Beta-coalescent absorption times

**Setting.** The Beta$(a,b)$-coalescent, $a,b>0$, is the $\Lambda$-coalescent with $\Lambda(dr)=\beta_{a,b}(dr)=r^{a-1}(1-r)^{b-1}dr$: with $p$ blocks, each given set of $k\ge2$ blocks merges at rate $\lambda_{p,k}=B(a+k-2,b+p-k)$, and the total merger rate with $k$ blocks is $\lambda_k=\int(1-(1-r)^k-kr(1-r)^{k-1})r^{-2}\Lambda(dr)$. Started from $n$ blocks, $\tau_n$ is the absorption time (time to one block) and $T^k_n$ the first time fewer than $k$ blocks remain. For $a>1$, $\tau_n/\log n\to1/\mu$ in probability, $\mu=\int|\log(1-r)|r^{-2}\Lambda(dr)$; for $a<1$ the coalescent comes down from infinity and $\tau_n$ converges in law to $\rho_\infty$.

**Rate function.** For $a>1$ let, for $y>-b$,
$$L_{a,b}(y)=\frac{\Gamma(a)}{(2-a)(a-1)}\Big(\frac{\Gamma(b+y)}{\Gamma(a+b+y-2)}-\frac{\Gamma(b)}{\Gamma(a+b-2)}\Big)\quad(a\neq2),\qquad L_{2,b}(y)=\psi(b+y)-\psi(b),$$
with $\psi$ the digamma function. $L_{a,b}$ is a concave increasing bijection from $(-b,\infty)$ onto $(-\infty,D_{a,b})$; let $\zeta_{a,b}$ be its inverse (convex, increasing, $+\infty$ beyond $D_{a,b}$) and $\mathcal{I}_{a,b}(x)=\sup_\theta\{\theta x-\zeta_{a,b}(\theta)\}$, so $\mathcal{I}_{a,b}=\infty$ on $(-\infty,0)$ and $\mathcal{I}_{a,b}(0)=b$. With $x_k=\zeta'_{a,b}(\lambda_k)$, the capped function is $\mathcal{I}^k_{a,b}(x)=\mathcal{I}_{a,b}(x)$ for $x\le x_k$ and $\mathcal{I}_{a,b}(x_k)+\lambda_k(x-x_k)$ for $x\ge x_k$.

**Statements.**
1. *(LDP, $a>1$.)* For every $k\ge2$, $(T^k_n/\log n)_{n\ge1}$ satisfies a large deviation principle with speed $\log n$ and good rate function $\mathcal{I}^k_{a,b}$; in particular $\tau_n/\log n=T^2_n/\log n$ has rate function $\mathcal{I}^2_{a,b}$, whose unique zero recovers the law of large numbers. Probabilities of atypical values decay polynomially, e.g. $\mathbb{P}(\tau_n\le\epsilon\log n)\approx n^{-\mathcal{I}^2_{a,b}(\epsilon)}$.
2. *(Convergence rate, $a<1$.)* If $b>1-a$, there is $C(a,b)$ with $d_K(\rho_n,\rho_\infty)\le C(a,b)\,n^{-(1-a)}$ for all $n$, where $d_K$ is the Kolmogorov distance and $\rho_n$ the law of $\tau_n$.
3. *(Records.)* For any finite $\Lambda$ with $\Lambda(\{0\})=0$, the record probability $\mathbb{P}(\tau_n\neq\tau_{n+1})$ equals a Laplace functional of the $\Lambda'$-coalescent (with $\Lambda'(dr)=(1-r)\Lambda(dr)$); for $\Lambda=\beta_{a,b}$, $a<1$, $b>1-a$, it is of exact order $n^{-(2-a)}$.

## Depends on

- [Beta-coalescents as Λ-coalescents](../multiple-merger-coalescents/merger-rates-and-beta-coalescents/beta-lambda.md)

## Expansion

Since $\tau_n=\int_0^{\tau_n}1\,ds$, the LDP reduces to the asymptotics of $\mathbb{E}[e^{\theta\int_0^{\tau_n}\psi(|\Pi^n_s|)ds}]$ for functions $\psi$. A statistical-mechanics style argument tilts the coalescent: the ratio $\lambda_n(\beta_{a,b'})/\lambda_n(\beta_{a,b})$ behaves like $1+(\text{const})\cdot L_{a,b}$-type corrections, so exponential functionals of the Beta$(a,b)$ coalescent are comparable to the change of measure to a Beta$(a,b+y)$ coalescent, giving $\frac{1}{\log n}\log\mathbb{E}e^{\theta\tau_n}\to\zeta_{a,b}(\theta)$ for $\theta<\lambda_2$; the Gärtner-Ellis theorem then produces $\mathcal{I}_{a,b}$, and the cap at slope $\lambda_k$ reflects that the last step from $k$ blocks is exponential with rate $\lambda_k$, so long excursions are cheapest by waiting there. For $a<1$, coupling $\tau_n$ and $\tau_{n+1}$ shows they differ only on a record event whose probability is a Laplace functional, and summing the tail gives the Kolmogorov rate.

## Sources

- Grégoire Véchambre, "Large deviation principle for the absorption time of the Beta-coalescent via integral functionals", arXiv:2512.17418 (2025), Section 2 (definitions of $L_{a,b}$, $\zeta_{a,b}$, $\mathcal{I}^k_{a,b}$, Theorems 2.1, 2.2, 2.5, 2.6, 2.8, Proposition 2.9 and Corollary 2.10), <https://doi.org/10.48550/arXiv.2512.17418>.
