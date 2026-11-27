# Selfing and oocyst parent sharing as a function of the complexity of infection

**Setting.** A vector feeds on a host infection carrying $n \ge 2$ mutually unrelated haploid strains (the complexity of infection) with within-host proportions $p = (p_1, \dots, p_n)$, $\sum_i p_i = 1$. Each of the $K \ge 1$ oocysts is formed by drawing two gametocytes independently from $p$, with replacement, so an oocyst is *selfed* when both draws are the same strain and *outcrossed* otherwise. Parasite pairs sampled from different oocysts are related only through parental strains those oocysts share.

**Proposition.**
1. The probability that an oocyst is selfed, and hence yields only genetic clones of one parental strain, is the Simpson index $\;\sigma(p) = \sum_{i=1}^n p_i^2$. With uniform proportions $\sigma = 1/n$; skewing the proportions raises it, since $\sigma(p) \ge 1/n$ with equality only at the uniform vector.
2. With uniform proportions, two independently formed oocysts share at least one parental strain with probability

$$q(n) = 1 - \frac1n\Bigl(\frac{n-1}{n}\Bigr)^{2} - \Bigl(1 - \frac1n\Bigr)\Bigl(\frac{n-2}{n}\Bigr)^{2} = \frac{4n^2 - 6n + 3}{n^3},$$

which is strictly decreasing in $n$ and satisfies $q(n) = 4/n + O(n^{-2})$. Hence $q(2) = 7/8$, $q(3) = 7/9$, $q(4) = 43/64$, and $q(20) = 1483/8000 \approx 0.19$.
3. A pair of outcrossed oocysts sharing exactly one parental strain (the half-sibling configuration) requires three distinct parental strains and so is possible only when $n \ge 3$; a pair of outcrossed oocysts sharing no parental strain, giving unrelated cotransmitted parasites, requires four and so is possible only when $n \ge 4$. (Selfed oocysts can share no parent already at $n = 2$, which is why $q(2) < 1$.)

**Consequence.** Since parasites drawn from one oocyst have expected relatedness $1/3$ while parasites from oocysts with no shared parent are unrelated, the expected relatedness of cotransmitted parasites falls as the complexity of infection rises, and the decline is steeper when more oocysts contribute, because multi-oocyst draws are then the typical case. Conversely, highly skewed strain proportions raise selfing and push cotransmission toward clones.

## Depends on

- [Relatedness of parasites sampled from a single outcrossed oocyst](relatedness-of-parasites-from-a-single-outcrossed-oocyst.md)

## Proof sketch

Statement 1 is the probability that two independent draws from $p$ coincide, $\sum_i p_i^2$, and $\sigma(p) - 1/n = \sum_i (p_i - 1/n)^2 \ge 0$. For statement 2, condition on the first oocyst's parent set: with probability $1/n$ it is a single strain and the second oocyst avoids it with probability $((n-1)/n)^2$; with probability $1 - 1/n$ it is two distinct strains, avoided with probability $((n-2)/n)^2$. Expanding, $(n-1)^2 + (n-1)(n-2)^2 = n^3 - 4n^2 + 6n - 3$, so $q(n) = 1 - (n^3 - 4n^2 + 6n - 3)/n^3 = (4n^2 - 6n + 3)/n^3 = 4/n - 6/n^2 + 3/n^3$, which decreases in $n$ for $n \ge 2$. Statement 3 is a counting constraint on the parental strains that the two oocysts use. The three-step structure of the argument (sampling gametocytes from the host, mating within the vector, sampling sporozoites into the next host) makes the complexity of infection and the oocyst count the two parameters that fix the mixture of kinship classes transmitted; the infected-hepatocyte count affects the variance of the realized relatedness but not which kinships are accessible.

## Sources

- W. Wong, E. A. Wenger, D. L. Hartl, D. F. Wirth, *Modeling the genetic relatedness of Plasmodium falciparum parasites following meiotic recombination and cotransmission*, PLoS Computational Biology 14 (2018), e1005923, <https://doi.org/10.1371/journal.pcbi.1005923>, PMCID PMC5777656. Results, "Transmission model description" (gametocyte sampling proportional to within-host strain proportions, oocysts as sampled gamete pairs), "In multiple oocyst transmission simulations" (half-sibling pedigrees require complexity of infection at least three and unrelated pedigrees at least four; relatedness of cotransmitted strains declines with complexity of infection) and Methods, "Model design: Modeling transmission" (Dirichlet strain proportions, skewed ratios raising selfing). The closed forms for the selfing and parent-sharing probabilities are derived here.
