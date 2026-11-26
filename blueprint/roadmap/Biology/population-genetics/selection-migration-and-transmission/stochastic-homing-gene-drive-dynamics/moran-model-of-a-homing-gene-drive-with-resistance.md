# Moran model of a homing gene drive with resistance alleles

Consider a population of $N$ diploid individuals at one locus with three allele classes: wild type $W$, CRISPR homing drive $D$ and drive-resistant $R$. The six unordered genotypes $\alpha \in \{WW, WD, WR, DD, DR, RR\}$ have reproductive rates $f_\alpha > 0$ and counts $N_\alpha$ with $\sum_\alpha N_\alpha = N$. Let $P \in [0,1]$ be the homing efficiency. One time step consists of three events.

1. **Mating.** Two parents are drawn without replacement, each with probability proportional to reproductive rate: genotype $\alpha$ is drawn with probability

$$\frac{f_\alpha N_\alpha}{\sum_\beta f_\beta N_\beta}.$$

2. **Offspring.** Gametes are produced with probabilities $q_\alpha^A$ (genotype $\alpha$ transmits allele $A$):

$$q_{WW}^W = q_{DD}^D = q_{RR}^R = 1, \quad q_{WD}^D = \frac{1+P}{2}, \quad q_{WD}^R = \frac{1-P}{2},$$

$$q_{WR}^W = q_{WR}^R = q_{DR}^D = q_{DR}^R = \tfrac12,$$

and all other $q_\alpha^A = 0$. For parents $\alpha, \beta$ the offspring genotype $\gamma = \gamma_1\gamma_2$ has probability

$$q_{\alpha\beta}^{\gamma} = \frac{q_\alpha^{\gamma_1} q_\beta^{\gamma_2} + q_\alpha^{\gamma_2} q_\beta^{\gamma_1}}{1 + \delta_{\gamma_1\gamma_2}},$$

with $\delta$ the Kronecker delta.
3. **Death.** One individual chosen uniformly at random dies, keeping the population size at $N$.

In a $WD$ heterozygote the wild-type allele is converted to $D$ with probability $P$; failed conversion produces a resistant allele $R$, which the drive can no longer cut. The process starts from $i$ drive homozygotes and $N - i$ wild-type homozygotes and runs until an allele fixes; because resistance is generated whenever homing fails, the typical outcome is a transient rise of the drive followed by its loss and fixation of $W$ or $R$.

## Expansion

The offspring formula symmetrizes over which parent contributes which allele; the factor $1/(1+\delta_{\gamma_1\gamma_2})$ avoids double counting homozygotes, so $\sum_\gamma q_{\alpha\beta}^\gamma = 1$. A generation equals $N$ reproduction events. Noble et al. simulate this chain (Equations 1 and 2 of their Methods) with $N = 500$, checking that the distributions of peak drive frequency narrow but keep their central tendency up to $N = 10^4$, and compare with the deterministic model of a homing drive obtained in the large-population limit. Even with homing efficiency $0.5$ and drive fitness $0.9$, releasing a few drive homozygotes in a population without standing resistance gives a mean peak drive frequency of about $35\%$ before resistance takes over, which is the basis for the claim that such drives are highly invasive. Standing resistant variation enters only through the initial condition and decreases the mean peak drive frequency approximately linearly.

## Sources

- C. Noble, B. Adlam, G. M. Church, K. M. Esvelt, M. A. Nowak, "Current CRISPR gene drive systems are likely to be highly invasive in wild populations", eLife 7 (2018), e33423, <https://doi.org/10.7554/eLife.33423> (PMC6014726), Materials and methods, "Well-mixed finite population model", Equations (1)–(2).
