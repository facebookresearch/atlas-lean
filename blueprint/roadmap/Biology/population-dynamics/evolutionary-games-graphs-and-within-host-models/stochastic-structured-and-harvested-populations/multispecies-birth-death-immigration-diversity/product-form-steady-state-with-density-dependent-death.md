# Product-form steady state with density-dependent death

**Model.** Species immigrate at rate $\alpha>0$, each individual reproduces within its species at constant rate $r>0$, and each individual dies at rate $\mu(N)>0$ depending on the total population size $N$ (a carrying capacity acting through death). With $c_k$ the number of species of size $k$, $C=\sum_kc_k$, $N=\sum_kkc_k$, the transitions are $c_1\to c_1+1$ at rate $\alpha$, $(c_k,c_{k+1})\to(c_k-1,c_{k+1}+1)$ at rate $rkc_k$, $(c_{k-1},c_k)\to(c_{k-1}+1,c_k-1)$ at rate $\mu(N)kc_k$ ($k\ge2$), and $c_1\to c_1-1$ at rate $\mu(N)c_1$. For increasing $\mu$, a steady state exists when $\lim_{N\to\infty}\mu(N)>r$.

**Theorem.** If a steady state exists, it is reversible and given by

$$
P(\vec c)=\frac{1}{Z_{\alpha,r}}\Bigl(\frac{\alpha}{r}\Bigr)^{C}\frac{r^{N}}{\prod_{n=1}^{N}\mu(n)}\prod_{i\ge1}\frac{1}{i^{c_i}c_i!},\qquad Z_{\alpha,r}=1+\sum_{n\ge1}\frac{1}{n!}\prod_{k=0}^{n-1}\frac{\alpha+rk}{\mu(k+1)} ,
$$

and the total population has $P(N)=Z_{\alpha,r}^{-1}\frac{1}{N!}\prod_{k=0}^{N-1}\frac{\alpha+rk}{\mu(k+1)}$. The moment generating function of the number of species is $\mathbb{E}e^{\xi C}=Z_{\alpha e^\xi,r}/Z_{\alpha,r}$, whence

$$
\mathbb{E}C=\alpha\,\mathbb{E}\Bigl[\sum_{k=0}^{N-1}\frac{1}{\alpha+rk}\Bigr],\qquad \mathrm{Var}\,C=\mathbb{E}C(1-\mathbb{E}C)+\alpha^2\,\mathbb{E}\Bigl[\Bigl(\sum_{k=0}^{N-1}\frac{1}{\alpha+rk}\Bigr)^2-\sum_{k=0}^{N-1}\frac{1}{(\alpha+rk)^2}\Bigr].
$$

If instead the birth rate depends on $N$ (constant $\mu$, rate $r(N)$), the law of $N$ is still $P(N)\propto\frac{1}{N!}\prod_{k=0}^{N-1}\frac{\alpha+r(k)k}{\mu}$, but the species-count chain is not reversible, so no such product form follows from detailed balance.

## Proof depends on

- [Species abundance law of the neutral birth–death–immigration process](species-abundance-law-of-the-neutral-birth-death-immigration-process.md)

## Expansion

Unwinding the detailed-balance relations $\mu(N)c_1P(\vec c)=\alpha P(c_1-1,\dots)$ and $\mu(N)kc_kP(\vec c)=(k-1)(c_{k-1}+1)rP(\dots,c_{k-1}+1,c_k-1,\dots)$ from the configuration with all mass in singletons gives the product form; one checks directly that it balances every pair of states. Conditionally on $N$, the species partition is the Ewens partition with parameter $\alpha/r$, independent of $\mu$, because a density-dependent death rate multiplies all death transitions by the same factor $\mu(N)$. A density-dependent birth rate destroys this, since splitting a birth among species of different sizes no longer factorizes. For $\mu(N)\equiv\mu$ the formulas reduce to the noninteracting model with $Z_{\alpha,r}=(1-r/\mu)^{-\alpha/r}$.

## Sources

- Renaud Dessalles, Maria D'Orsogna, Tom Chou, *Exact steady-state distributions of multispecies birth–death–immigration processes: effects of mutations and carrying capacity on diversity*, arXiv (2018). Section 5 (model with carrying capacity: steady-state statistics; carrying capacity on birth) and Appendix C (steady-state distribution of the species counts). <https://doi.org/10.48550/arXiv.1806.00105> Published version: J Stat Phys, 173, 182-221, (2018), <https://doi.org/10.1007/s10955-018-2128-4>.
