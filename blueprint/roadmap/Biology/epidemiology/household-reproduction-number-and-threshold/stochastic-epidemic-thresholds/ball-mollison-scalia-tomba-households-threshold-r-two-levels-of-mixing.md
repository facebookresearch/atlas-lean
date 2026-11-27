# Threshold for epidemics with two levels of mixing

In the households SIR epidemic, individuals are grouped into small households; the contact rate between two members of the same household is $\lambda_H$, the contact rate between two individuals of different households is $\lambda_G/n$, and infectious periods are i.i.d. with mean $1/\gamma$. Britton (2010, Section 5), summarizing Ball, Mollison and Scalia-Tomba (1997), explains that external infections in the early phase nearly always hit previously uninfected households, so that, treating households as individuals, the early epidemic is approximated by a branching process; its reproduction number is $R_* = (\lambda_G/\gamma)\,\mu_H$, where $\mu_H$ is the mean size of a within-household outbreak in a household whose size has the size-biased distribution, and major outbreaks are possible only if $R_* > 1$. Pellis, Ball and Trapman (2012, Section 2.3) describe the same [household reproduction number](../household-r.md) as the offspring mean of the household-level branching process, whose generations consist of households reached from the local epidemics of the previous generation.

## Proof depends on

- [Galton–Watson extinction criterion](../../../../Probability/branching-processes/galton-watson-process/extinction-prob-eq-one-iff.md)

## Expansion

1. The model: households, the local and global contact processes, and the infectious-period distribution.
2. The household-level branching process and its mean offspring $R_*$, with the [Galton–Watson extinction criterion](../../../../Probability/branching-processes/galton-watson-process/extinction-prob-eq-one-iff.md).
3. The coupling of the early epidemic with this branching process as the number of households grows.
4. The threshold statement, the limit of the probability of a major outbreak, and the law of large numbers and central limit theorem for the final size of a major outbreak proved by Ball, Mollison and Scalia-Tomba, as separate statements.

## Sources

- T. Britton, Stochastic epidemic models: a survey, Math. Biosci. 225 (2010), 24–35, Section 5 (households). <https://arxiv.org/abs/0910.4443>
- L. Pellis, F. Ball and P. Trapman, Reproduction numbers for epidemic models with households and other social structures. I. Definition and calculation of $R_0$, Math. Biosci. 235 (2012), 85–97, Section 2.3. <https://doi.org/10.1016/j.mbs.2011.10.009>
- Original result: F. Ball, D. Mollison and G. Scalia-Tomba, Epidemics with two levels of mixing, Ann. Appl. Probab. 7 (1997), 46–89. <https://doi.org/10.1214/aoap/1034625252> The threshold $R_* = (\lambda_G/\gamma)\mu_H$ follows Britton (2010, Section 5).
