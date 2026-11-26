# Species abundance law of the neutral birth–death–immigration process

**Model.** Individuals of a new species immigrate at rate $\alpha>0$; each individual gives birth to an offspring of its own species at rate $r$ and dies at rate $\mu$, independently. Let $c_k$ be the number of species with exactly $k$ individuals, $C=\sum_kc_k$ the number of species and $N=\sum_kkc_k$ the number of individuals. A steady state exists if and only if $r<\mu$.

**Theorem.** If $r<\mu$, the stationary law of the species-count vector $\vec c=(c_1,c_2,\dots)$ is

$$
P(\vec c)=\Bigl(1-\frac{r}{\mu}\Bigr)^{\alpha/r}\Bigl(\frac{\alpha}{r}\Bigr)^{C}\Bigl(\frac{r}{\mu}\Bigr)^{N}\prod_{i\ge1}\frac{1}{i^{c_i}\,c_i!},
$$

and it satisfies detailed balance. Consequently:

1. the $c_k$ are independent, $c_k\sim\mathrm{Poisson}\bigl(\frac{\alpha}{r}\frac{1}{k}(\frac{r}{\mu})^k\bigr)$;
2. $N$ is negative binomial with parameters $\alpha/r$ and $r/\mu$: $P(N)=(1-r/\mu)^{\alpha/r}(r/\mu)^N\frac{1}{N!}\prod_{k=0}^{N-1}(\frac{\alpha}{r}+k)$, with $\mathbb{E}N=\frac{\alpha/\mu}{1-r/\mu}$ and $\mathrm{Var}\,N=\frac{\alpha/\mu}{(1-r/\mu)^2}$;
3. $C\sim\mathrm{Poisson}\bigl(\frac{\alpha}{r}\log\frac{1}{1-r/\mu}\bigr)$;
4. the size $n_i$ of a given species follows Fisher's logarithmic series law, independent of $\alpha$:

$$
P(n_i=k)=\frac{-1}{\log(1-r/\mu)}\,\frac{1}{k}\Bigl(\frac{r}{\mu}\Bigr)^k,\qquad k\ge1;
$$

5. for any $f$, $\mathbb{E}[c_kf(N)]=\frac{1}{k}\frac{\alpha}{r}(\frac{r}{\mu})^k\,\mathbb{E}[f(N+k)]$, which gives the expected Shannon entropy and Simpson index of the abundance distribution.

**Mutation at birth.** If each newborn founds a new species with probability $\epsilon\in[0,1]$, $P(N)$ is unchanged, species sizes follow the logarithmic series law with parameter $r(1-\epsilon)/\mu$, and

$$
\mathbb{E}C=\frac{\alpha/\mu}{1-r/\mu}\,\log\Bigl(\frac{1}{1-r(1-\epsilon)/\mu}\Bigr)\,\frac{1-r(1-\epsilon)/\mu}{r(1-\epsilon)/\mu}.
$$

## Expansion

The total population is a birth–death chain with rates $\alpha+rN$ and $\mu N$, whose detailed balance $\mu NP(N)=(\alpha+(N-1)r)P(N-1)$ gives the negative binomial law. On species counts, immigration moves $c_1\to c_1+1$ at rate $\alpha$, a birth moves a species from size $k$ to $k+1$ at rate $rkc_k$, and a death from $k$ to $k-1$ at rate $\mu kc_k$; the displayed product form balances each pair of these moves. Its factorization $\prod_k e^{-\theta_k}\theta_k^{c_k}/c_k!$ with $\theta_k=\frac{\alpha}{r}\frac{1}{k}(r/\mu)^k$ is the Ewens-type structure, and summing $\theta_k$ gives the Poisson mean of $C$ while $\mathbb{E}c_k=\mathbb{E}C\cdot P(n_1=k)$ gives the logarithmic series. With mutation the dynamics of a single species is a birth–death process with birth rate $r(1-\epsilon)$, so the abundance law changes only through that parameter, and $\mathbb{E}N=\mathbb{E}C\,\mathbb{E}n_1$ yields $\mathbb{E}C$.

## Sources

- Renaud Dessalles, Maria D'Orsogna, Tom Chou, *Exact steady-state distributions of multispecies birth–death–immigration processes: effects of mutations and carrying capacity on diversity*, arXiv (2018). Section 3 (simple birth–death–immigration model: steady-state statistics) and Section 4 (model with mutation). <https://doi.org/10.48550/arXiv.1806.00105> Published version: J Stat Phys, 173, 182-221, (2018), <https://doi.org/10.1007/s10955-018-2128-4>.
