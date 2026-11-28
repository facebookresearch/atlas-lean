# Fixation time of a double beneficial genotype under recombination

**Setting.** A population of fixed size $N$ carries two loci with alleles $a/A$ and $b/B$; initially every individual is of type $ab$. Each $a$ (resp. $b$) allele mutates to the beneficial allele $A$ (resp. $B$) at rate $\mu_N$. Individuals carrying $0$, $1$ and $2$ beneficial alleles die at rates $1$, $1-s_N$ and $1-2s_N$. When an individual dies it is replaced: with probability $1-r_N$ the newborn copies both alleles from one uniformly chosen individual; with probability $r_N$ (recombination) it takes the $a/A$ allele from one uniformly chosen individual and the $b/B$ allele from an independently chosen one. Write $\ln_+(x) = \ln x$ for $x > 1$ and $\ln_+(x) = 0$ for $x \in [0,1]$. Assume $\mu_N \in (0,1)$, $s_N \in (0,1/2]$, $r_N \in [0,1)$ and, as $N \to \infty$,

$$s_N \ll 1, \qquad 1 \ll N\mu_N, \qquad N\mu_N^2 \ll s_N, \qquad r_N \ln_+(N r_N) \ll s_N,$$

where $a_N \ll b_N$ means $a_N/b_N \to 0$.

**Theorem.** Let $T$ be the first time at which every individual is of type $AB$, and set

$$t^*_N(r) = \frac{1}{s_N}\ln\left(\frac{N s_N^3}{\mu_N \max\{N\mu_N^2,\ r\ln_+(N r)\}}\right).$$

Then for every $\theta \in (0,1)$,

$$\lim_{N\to\infty} \mathbb{P}\big((1-\theta)\,t^*_N(r_N) \le T \le (1+\theta)\,t^*_N(r_N)\big) = 1.$$

Thus $T/t^*_N(r_N) \to 1$ in probability. In the *mutation-dominating* regime $N\mu_N^2 \ge r_N\ln_+(Nr_N)$ the first $AB$ individuals arise mainly by a second mutation on a single-mutant background, and $t^*_N$ does not depend on $r_N$; in the *recombination-dominating* regime $r_N\ln_+(Nr_N) > N\mu_N^2$ they arise mainly by recombination between $Ab$ and $aB$ individuals, and $t^*_N$ decreases as $r_N$ grows. This is a rigorous form of the Fisher–Muller hypothesis that recombination speeds up adaptation.

## Depends on

- [Hill–Robertson interference](../hill-robertson-interference.md)

## Expansion

The proof splits the trajectory into four phases. In phase 1 single mutants $Ab$ and $aB$ grow from recurrent mutation; their counts stay close to the deterministic logistic solution, reaching a positive fraction $e^{-C_1}N$ of the population at time of order $s_N^{-1}\ln(Ns_N/\mu_N)$. Meanwhile $AB$ individuals are produced at rate of order $N\mu_N^2$ (mutation) or $Nr_N\ln(Nr_N)$ (recombination, the logarithm coming from the integrated product of the single-mutant frequencies), so the $AB$ count at the end of phase 2 is of order $N\max\{N\mu_N^2, r_N\ln(Nr_N)\}/s_N$. In phases 3 and 4 the $AB$ class has an advantage $s_N$ over single mutants and grows exponentially until it takes over; the time needed is $s_N^{-1}$ times the logarithm of $N$ over its initial size, which gives the formula for $t^*_N$. Each phase is controlled by martingales and submartingales built from the birth, death, mutation and recombination rates, together with a density-dependent law of large numbers for the middle phase.

## Sources

- Nantawat Udomchatpitak, "The Effect of Recombination on the Speed of Evolution", *ALEA Lat. Am. J. Probab. Math. Stat.* 18(1) (2021), 547. <https://doi.org/10.30757/ALEA.v18-23>
- Preprint version (the locators in this item follow its numbering): Nantawat Udomchatpitak, "The Effect of Recombination on the Speed of Evolution", arXiv:1904.09922 (2019), Section 1.3 (parameter conditions) and Theorem 1; Propositions 2–5 (phase estimates), <https://doi.org/10.48550/arXiv.1904.09922>.
