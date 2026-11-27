# Expected segregating sites during build-up from a monomorphic state

In the Poisson random field model started at time $0$ from a monomorphic population (new mutations at rate $N\theta$, each starting at frequency $1/N$, Wright–Fisher diffusion with scaled selection $\gamma$), take a sample of size $m \ge 2$ at time $t$. The numbers $Z^{N,k}_t$ of sites with exactly $k$ derived copies in the sample, $1 \le k \le m$, are independent Poisson variables, and as $N \to \infty$

$$ \mathbb{E}\, Z^{N,k}_t \to \theta \binom{m}{k} \omega_\gamma \int_0^1 \mathbb{P}^{*\gamma}_{1-y}(\tau_1 \le t)\, y^k (1-y)^{m-k}\, \pi_\gamma(y)\, dy . $$

Summing over $1 \le k \le m-1$ with $a_m(y) = 1 - y^m - (1-y)^m$, the limiting expected number of segregating sites in the sample is

$$ S_m(t) = \theta\omega_\gamma \int_0^1 \mathbb{P}^{*\gamma}_{1-y}(\tau_1\le t)\, a_m(y)\, \pi_\gamma(y)\, dy . $$

Under neutrality ($\gamma = 0$), with $m_{[k]}$ and $m_{(k)}$ the falling and rising factorials,

$$ S_m(t) = \theta \sum_{k=2}^{m} \big(1+(-1)^k\big)\big(1 - e^{-\binom{k}{2}t}\big)\, \frac{2k-1}{\binom{k}{2}}\, \frac{m_{[k]}}{m_{(k)}} , $$

which recovers the fixed-population-size expression of Tajima. For example $S_2(t) = 2\theta(1-e^{-t})$ and $S_3(t) = 3\theta(1-e^{-t})$, increasing to the stationary values $2\theta$ and $3\theta$. For $\gamma \le 0$ one also has $S_m(t) = 2\theta\,\mathbb{E}^{-\gamma}_\infty\big[\sum_{k=0}^{m-1} (k+A_t)^{-1} - \Gamma(A_t)\Gamma(m)/\Gamma(A_t+m)\big]$ with $A_t$ the dual process.

## Depends on

- [Non-equilibrium allele frequency spectrum](non-equilibrium-allele-frequency-spectrum.md)
- [Coalescent dual representation of the non-equilibrium allele frequency spectrum](coalescent-dual-representation-of-the-non-equilibrium-allele-frequency-spectrum.md)

## Expansion

Binomial sampling of a site at population frequency $y$ gives $k$ derived copies with probability $\binom{m}{k}y^k(1-y)^{m-k}$, a function in $\mathcal{F}_0$ for $1\le k \le m-1$, so the non-equilibrium spectrum theorem applies term by term. In the neutral case one can instead use duality directly: $\mathbb{E}^0 Z^N_m(t) = \theta\int_0^t N\,\mathbb{E}^0_m[1 - N^{-A_u} - (1-1/N)^{A_u}]\,du \to \theta\int_0^t(\mathbb{E}^0_m A_u - \mathbb{P}^0_m(A_u=1))\,du$, and the explicit Kingman transition probabilities give the series.

## Sources

- Ingemar Kaj and Carina F. Mugal, *The non-equilibrium allele frequency spectrum in a Poisson random field framework*, Theor. Popul. Biol. 111 (2016), 51–64. <https://doi.org/10.1016/j.tpb.2016.06.003> Section 4 (population and sample functionals; expected segregating sites, the equation for $S_m(t)$ and its neutral series). Locators use the numbering of the preprint arXiv:1512.04925.
