# Probability of no recombination before the two-locus most recent common ancestor

In the two-locus ancestral process $(a(t), b(t), c(t))$ (lineages ancestral at locus $A$ only, at $B$ only, at both loci) with scaled recombination rate $\rho > 0$ and coalescence rate $1$ per pair, let $\tau$ be the absorption time into $\mathcal S = \{(1,1,0),(0,0,1)\}$ (the sample has a common ancestor at both loci), and let $s(t)$ count the recombination events on ancestral lineages up to time $t$.

**Theorem.**

1. For a sample of $n \ge 1$ gametes all typed at both loci, started from $(0,0,n)$,

$$\mathbb P_{0,0,n}[s(\tau) = 0] = \frac{(n-1)!}{(\rho+1)_{n-1}} = \prod_{i=1}^{n-1}\frac{i}{i+\rho},$$

where $(\rho+1)_{k} = (\rho+1)(\rho+2)\cdots(\rho+k)$ is the rising factorial.

2. For a sample of $n$ gametes typed at locus $A$ only together with one gamete typed at both loci, started from $(n,0,1)$,

$$\mathbb P_{n,0,1}[s(\tau) = 0] = \prod_{i=1}^{n}\frac{i(i+1)}{i(i+1)+\rho}.$$

More generally, for any start $(l,m,n)$, $\mathbb P_{l,m,n}[s(\tau)=0] = \mathbb E_{l,m,n}\big[\exp\{-\tfrac\rho2\int_0^{\tau_0} c_0(u)\,du\}\big]$, where $(a_0,b_0,c_0)$ is the chain with recombination switched off and $\tau_0$ its absorption time, and the expected number of recombinations before $\tau$ is $\mathbb E_{l,m,n}[s(\tau)] = \tfrac\rho2\,\mathbb E_{l,m,n}\big[\int_0^\tau c(u)\,du\big]$.

## Depends on

- [Moment duality between the two-locus Wright–Fisher diffusion and the ancestral process with recombination](two-locus-wright-fisher-moment-duality.md)
- [Two-locus ancestral process for n sequences](../two-locus-ancestral-process-for-n-sequences.md)

## Expansion

Recombination only acts on doubly ancestral lineages, at rate $\rho/2$ each, so conditioning on no recombination is an exponential killing of the recombination-free chain at rate $\tfrac\rho2 c_0$. From $(0,0,n)$ the recombination-free chain stays on $(0,0,i)$ and is a pure death process with rate $\binom i2$; in each state the probability of no recombination during the holding time is $\binom i2/(\binom i2 + i\rho/2) = (i-1)/(i-1+\rho)$, and the strong Markov property multiplies these over $i = n, \dots, 2$. From $(n,0,1)$ the chain stays on $(i,0,1)$ with death rate $\binom i2 + i = i(i+1)/2$ and killing rate $\rho/2$, giving the factor $i(i+1)/(i(i+1)+\rho)$ for $i = n,\dots,1$. (The source prints the second product with index starting at $i = 0$; the $i = 0$ factor would vanish, and the state $(0,0,1)$ is already absorbing, so the product runs over $i \ge 1$.)

## Sources

- Shuhei Mano, "Duality between the two-locus Wright–Fisher diffusion model and the ancestral process with recombination", *Journal of Applied Probability* 50 (2013), 256–271, <https://doi.org/10.1239/jap/1363784437>; preprint arXiv:1201.5557, <https://doi.org/10.48550/arXiv.1201.5557>. Numbering of the arXiv version: Lemma 5.6, Corollaries 5.7 and 5.9, Theorems 5.10 and 5.11.
