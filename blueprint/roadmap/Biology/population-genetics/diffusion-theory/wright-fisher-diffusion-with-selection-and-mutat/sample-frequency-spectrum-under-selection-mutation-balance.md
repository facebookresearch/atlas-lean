# Sample frequency spectrum of a two-state marker under selection–mutation balance

Consider a biallelic (or two-state epigenetic) marker with states $U$ and $M$ in a randomly mating diploid population of constant effective size $N_e$ at mutation–selection–drift equilibrium. Let $\mu$ be the per-generation rate $U \to M$, $\nu$ the rate $M \to U$, and $s$ the semidominant selective advantage of $U$ over $M$; set

$$\alpha = 4N_e\mu, \qquad \beta = 4N_e\nu, \qquad \gamma = 4N_es.$$

In the diffusion limit the frequency $x$ of state $U$ has Wright's stationary density proportional to

$$e^{\gamma x}\,x^{\beta-1}(1-x)^{\alpha-1}, \qquad 0 < x < 1.$$

**Proposition.** For $\alpha, \beta > 0$, the probability that a sample of $n$ chromosomes carries exactly $k$ copies of $U$ and $n-k$ copies of $M$ is

$$p_k = \binom nk\frac{{}_1F_1(\beta+k;\ \alpha+\beta+n;\ \gamma)\,(\beta)_k\,(\alpha)_{n-k}}{{}_1F_1(\beta;\ \alpha+\beta;\ \gamma)\,(\alpha+\beta)_n}, \qquad k = 0,1,\dots,n,$$

where ${}_1F_1$ is Kummer's confluent hypergeometric function and $(x)_m = x(x+1)\cdots(x+m-1)$ is the Pochhammer symbol. If instead $M$ is favored, exchange $\alpha$ and $\beta$ (and use the selective advantage of $M$). For loci $j$ with independent histories and $d_k$ loci observed with $k$ copies of $U$, the likelihood of $(\mu,\nu,s)$ is $L = \prod_{k=0}^n p_k^{d_k}$, using both segregating and fixed classes.

## Depends on

- [Partition function of the selection–mutation stationary density](selection-mutation-partition.md)

## Expansion

$p_k = \binom nk\,\mathbb E[x^k(1-x)^{n-k}]$ under the stationary law. Using $\int_0^1 e^{\gamma x}x^{a-1}(1-x)^{b-1}\,dx = B(a,b)\,{}_1F_1(a;a+b;\gamma)$ for $a,b>0$ in the numerator (with $a = \beta+k$, $b = \alpha+n-k$) and denominator (with $a = \beta$, $b = \alpha$), the ratio of beta functions is $B(\beta+k,\alpha+n-k)/B(\beta,\alpha) = (\beta)_k(\alpha)_{n-k}/(\alpha+\beta)_n$. With $\gamma = 0$ the formula reduces to the beta-binomial sample distribution of the neutral two-allele model. This density is the selection–mutation stationary density with genic selection coefficient $\gamma/2$ and mutation parameters $\theta_1 = \beta$, $\theta_2 = \alpha$.

## Sources

- Aline Muyle, Jeffrey Ross‐Ibarra and Danelle K. Seymour, "Gene body methylation is under selection in Arabidopsis thaliana", Genetics (2021), <https://doi.org/10.1093/genetics/iyab061> (PMC8225343). Methods, "Estimation of selection using the site frequency spectrum", Eqs. (2)–(3) (model of Charlesworth and Jain, Genetics 2014).
