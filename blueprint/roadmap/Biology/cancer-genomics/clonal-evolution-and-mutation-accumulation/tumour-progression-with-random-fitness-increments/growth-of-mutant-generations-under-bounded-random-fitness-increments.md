# Growth of mutant generations under bounded random fitness increments

**Model.** A tumour starts from a type-0 population growing deterministically as $Z_0(t)=V_0e^{\lambda_0t}$, where $\lambda_0=a_0-d_0>0$ is the net growth rate of type-0 cells (birth rate $a_0$, death rate $d_0$). Type-$(k-1)$ cells give rise to type-$k$ mutants at rate $u_k$ per cell. Every mutation adds an independent random amount $X\sim\nu$ to the birth rate of the new lineage (death rate stays $d_0$), and each mutant founds a linear birth–death branching process. $Z_k(t)$ is the number of type-$k$ cells at time $t$. Assume $\nu$ has a density $g$ supported on $[0,b]$ with

$$(\ast)\qquad g \text{ continuous at } b,\quad g(b)>0,\quad g\le G \text{ on } [0,b].$$

**Theorem (first generation).** Under $(\ast)$, with $p=b/\lambda_0$:

*(1)* $\displaystyle \mathbb E Z_1(t)\sim\frac{V_0u_1\,g(b)}{b\,t}\,e^{(\lambda_0+b)t}$.

*(2)* For $\theta\ge0$,

$$\mathbb E\exp\!\big(-\theta\,t^{1+p}e^{-(\lambda_0+b)t}Z_1(t)\big)\to\exp\!\big(-V_0u_1\,\theta^{\lambda_0/(\lambda_0+b)}\,c_1(\lambda_0,b)\big),$$

with

$$c_1(\lambda_0,b)=\frac{g(b)}{\lambda_0}\Big(\frac{a_0+b}{\lambda_0+b}\Big)^{-b/(\lambda_0+b)}\Gamma\!\Big(\frac{\lambda_0}{\lambda_0+b}\Big)\Gamma\!\Big(1-\frac{\lambda_0}{\lambda_0+b}\Big),$$

so $t^{1+p}e^{-(\lambda_0+b)t}Z_1(t)\Rightarrow V_1$, a one-sided stable law of index $\lambda_0/(\lambda_0+b)$ with $\Pr(V_1>v)\asymp v^{-\lambda_0/(\lambda_0+b)}$.

*(3)* $V_1$ is the sum of the points of a Poisson process on $(0,\infty)$ with mean measure $\mu(z,\infty)=A_1(\lambda_0,b)\,u_1V_0\,z^{-\lambda_0/(\lambda_0+b)}$ for an explicit constant $A_1$: many mutant lineages contribute to the first generation.

**Theorem ($k$-th generation).** Define $p_k$ and $u_{1,k}$ by

$$k+p_k=\sum_{j=0}^{k-1}\frac{\lambda_0+kb}{\lambda_0+jb},\qquad u_{1,k}=\prod_{j=1}^{k}u_j^{\lambda_0/(\lambda_0+(j-1)b)}.$$

Under $(\ast)$,

$$\mathbb EZ_k(t)\sim\frac{V_0\,u_1\cdots u_k\,g(b)^k}{t^k\,b^k\,k!}\,e^{(\lambda_0+kb)t},$$

while

$$\mathbb E\exp\!\big(-\theta\,t^{k+p_k}e^{-(\lambda_0+kb)t}Z_k(t)\big)\to\exp\!\big(-c_k(\lambda_0,b)\,V_0u_{1,k}\,\theta^{\lambda_0/(\lambda_0+kb)}\big),$$

so $t^{k+p_k}e^{-(\lambda_0+kb)t}Z_k(t)\Rightarrow V_k$. Since $p_k>0$, the mean overstates the typical size by a polynomial factor in every generation.

## Expansion

Mutations to type 1 form a Poisson process on $[0,t]\times[0,b]$ with intensity $V_0e^{\lambda_0s}\,ds\,g(x)dx$, a point $(s,x)$ meaning a mutant born at time $s$ with birth rate $a_0+x$. Conditioning on this process gives the exact Laplace transform

$$\mathbb Ee^{-\theta Z_1(t)}=\exp\Big(-u_1\int_0^b g(x)\int_0^tV_0e^{\lambda_0s}\big(1-\tilde\phi_{x,t-s}(\theta)\big)\,ds\,dx\Big),$$

where $\tilde\phi_{x,r}$ is the Laplace transform of a birth–death process with rates $a_0+x,d_0$ started from one cell. The dominant contribution comes from increments $x=b-O(1/t)$ born near time $(\log t)/\lambda_0$: the density near $b$ produces the $1/t$ in the mean, and the timing produces the extra $t^{-p}$ in the typical size. Each surviving lineage grows like $\zeta e^{(\lambda_0+x)(t-s)}$ with $\zeta$ exponential, which turns the limit into a sum over a Poisson point process with power-law intensity. For later generations one treats type-1 lineages as a three-dimensional Poisson process of (time, increment, limiting size) and inducts, each generation adding a delay $(\log t)/(\lambda_0+jb)$; this gives the exponent $k+p_k$.

These are Theorems 1–5 of the source (Theorems 1–3 for $Z_1$, Theorems 4–5 for $Z_k$).

## Sources

- R. Durrett, J. Foo, K. Leder, J. Mayberry, F. Michor, *Evolutionary dynamics of tumor progression with random fitness values*, Theoretical Population Biology 78 (2010); arXiv:1003.1927. <https://doi.org/10.48550/arXiv.1003.1927>
