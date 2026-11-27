# Gene flow factor after a single admixture pulse

A recipient population is fixed for alleles $S_2$ (selected locus) and $N_2$ (linked neutral locus); a donor population is fixed for $S_1$ and $N_1$. A single admixture pulse at time $0$ introduces the haplotype $N_1S_1$ at frequency $p_0$. In the recipient, carriers of $S_1$ have viability $1-s$ ($0 \le s < 1$; carriers are heterozygous, since $S_1S_1$ homozygotes are rare and ignored), and the recombination fraction between the loci is $r \in [0, \tfrac12]$. To first order in $p_0$ the expected frequency of $N_1$ after $t$ generations is $p_t = p_0\,f(r,s,t)$. If $r = s = 0$ the recursions below preserve $p_0$, so $f_a = f_X = 1$ for every $t$. Otherwise $r + s > 0$, so $c = (1-s)(1-r) < 1$ and $(1 - \tfrac23 r)(1-s) < 1$, and

**Autosome.**

$$f_a(r,s,t) = \frac{c^{\,t}\,[\,1 - r - c\,] + r}{1 - c} = c^{\,t} + \frac{r\,(1 - c^{\,t})}{1 - c}.$$

**X chromosome (non-pseudoautosomal), equal fitness $1-s$ in carrier females and males, female recombination fraction $r$.** An X-linked allele spends on average a fraction $2/3$ of generations in females, so the effective recombination fraction is $\tfrac23 r$:

$$f_X(r,s,t) = \frac{s\,(1 - \tfrac23 r)^{t+1}(1-s)^t + \tfrac23 r}{1 - (1-\tfrac23 r)(1-s)}.$$

**Limit.** For $r + s > 0$, as $t\to\infty$,

$$f_a(r,s,t) \to \frac{r}{1 - (1-s)(1-r)} = \frac{r}{r + s - rs},$$

the gene flow factor: the fraction of the introgressed neutral allele that escapes the barrier created by the linked deleterious allele.

## Proof sketch

Let $x_t$ be the frequency of $N_1$ still on the $S_1$ background and $y_t$ the frequency already on $S_2$. Each generation a fraction $r$ of the linked copies recombines onto $S_2$ and escapes selection, and the rest survive with probability $1-s$: $x_{t+1} = (1-r)(1-s)x_t = c\,x_t$ and $y_{t+1} = y_t + r x_t$. Hence $x_t = c^t p_0$, $y_t = r p_0 (1 + c + \cdots + c^{t-1}) = r p_0 (1-c^t)/(1-c)$, and $p_t = x_t + y_t$ gives $f_a$. Replacing $r$ by $\tfrac23 r$ and using $1 - c - \tfrac23 r = s(1-\tfrac23 r)$ gives $f_X$. In an equilibrium single-pulse model, the limit coincides with the classical gene flow factor of hybrid-zone theory.

## Sources

- I. Jurić, S. Aeschbacher and G. Coop, "The strength of selection against Neanderthal introgression", PLoS Genetics 12 (2016), e1006340, Methods ("Model", Equations 1–5; "Inference procedure", Equations 6–7), <https://doi.org/10.1371/journal.pgen.1006340> (PMC5100956).
- K. Harris and R. Nielsen, "The genetic cost of Neanderthal introgression", Genetics 203 (2016), 881–891, Equations 1–2 and the following paragraph, <https://doi.org/10.1534/genetics.116.186890> (PMC4896200).
