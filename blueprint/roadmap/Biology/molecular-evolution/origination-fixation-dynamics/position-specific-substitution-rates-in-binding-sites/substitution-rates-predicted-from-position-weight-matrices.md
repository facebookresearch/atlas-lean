# Substitution rates predicted from position weight matrices

Let $P_{ab}$ ($a \neq b$) be the position-independent mutation rate from nucleotide $a$ to $b$, and let $f_{ap} > 0$ be the frequency of nucleotide $a$ at position $p$ of a binding-site position weight matrix, interpreted as the stationary base distribution under the selective constraint at $p$. Under the weak-mutation (origination–fixation) model with Kimura's fixation probability, the substitution rate from $a$ to $b$ at position $p$ satisfies

$$R_{abp} \propto P_{ab}\, \frac{\ln\!\Bigl(\dfrac{f_{bp} P_{ba}}{f_{ap} P_{ab}}\Bigr)}{1 - \dfrac{f_{ap} P_{ab}}{f_{bp} P_{ba}}},$$

with the ratio read as its limit $1$ when $f_{bp} P_{ba} = f_{ap} P_{ab}$, and the predicted rate of evolution at position $p$ is

$$K_p = \sum_{a} f_{ap} \sum_{b \neq a} R_{abp} .$$

Positions where the factor tolerates a single base ($f_{bp} \to 0$ for $b \neq a$) have $R_{abp} \to 0$, while positions without preference and symmetric mutation ($f_{ap} = 1/4$, $P_{ab} = P_{ba}$) evolve at the mutation rate.

## Depends on

- [Information content of a position weight matrix column](../../../bioinformatics/position-weight-matrices/info-content.md)

## Expansion

In the weak-mutation regime the substitution rate is $R_{abp} = 2N P_{ab}\, \Pr(\text{fixation})$, and with scaled selection coefficient $S$ Kimura's formula gives $2N\Pr(\text{fixation}) \approx S/(1 - e^{-S})$. Requiring the stationary distribution of the resulting reversible chain to equal the observed frequencies forces $S_{abp} = \ln\bigl(f_{bp}P_{ba}/(f_{ap}P_{ab})\bigr)$, and substituting yields the displayed proportionality (Halpern and Bruno's relation). Writing $y = f_{bp}P_{ba}/(f_{ap}P_{ab})$, the factor $\ln y/(1 - 1/y)$ tends to $1$ as $y \to 1$ and to $0$ as $y \to 0$. Constrained, high-information positions are therefore predicted to evolve slowly. In four aligned yeast species the source observed that binding sites evolve more slowly than their promoters, that substitutions per position correlate negatively with information content (Spearman correlations from $-0.70$ to $-0.84$ in six of seven factors), and that predicted and observed per-position rates agree with $R^2 = 0.67$ using an HKY85 background mutation model.

## Sources

- A. M. Moses, D. Y. Chiang, M. Kellis, E. S. Lander and M. B. Eisen, "Position specific variation in the rate of evolution in transcription factor binding sites", *BMC Evolutionary Biology* 3 (2003), 19, Results section "Using the proportionality of Halpern and Bruno" and Methods, <https://doi.org/10.1186/1471-2148-3-19> (PMC212491).
- A. L. Halpern and W. J. Bruno, "Evolutionary distances for protein-coding sequences: modeling site-specific residue frequencies", *Molecular Biology and Evolution* 15 (1998), 910–917, <https://doi.org/10.1093/oxfordjournals.molbev.a025995>.
