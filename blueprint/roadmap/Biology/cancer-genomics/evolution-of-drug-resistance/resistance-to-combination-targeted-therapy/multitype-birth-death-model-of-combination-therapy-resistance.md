# Multitype birth–death model of resistance to combination therapy

Consider treatment with two drugs. Every cell has one of four types $00, 10, 01, 11$, where a $1$ in the first (second) position means resistance to drug 1 (drug 2). Fix a point-mutation rate $u > 0$ and nonnegative integers $n_1, n_2, n_{12}$: the numbers of point mutations that confer resistance to drug 1 only, to drug 2 only, and to both drugs (cross-resistance).

**Pretreatment phase.** The process starts from one type-$00$ cell. Every cell divides at rate $b$ and dies at rate $d$, with $0 < d < b$. At a division, the offspring of a type-$00$ cell is of type $10$ with probability $u n_1$, of type $01$ with probability $u n_2$, of type $11$ with probability $u n_{12}$, and of type $00$ otherwise; the offspring of a type-$10$ cell is of type $11$ with probability $u(n_2 + n_{12})$ and of type $10$ otherwise (symmetrically for type $01$); type $11$ breeds true. The phase ends when the lesion first contains $M$ cells.

**Treatment phase.** Cells of types $00, 10, 01$ (sensitive to at least one drug) divide at rate $b'$ and die at rate $d' > b'$; type-$11$ cells keep the rates $b, d$; mutation probabilities are unchanged. Write

$$s = 1 - \frac{d}{b} \in (0, 1), \qquad s' = 1 - \frac{d'}{b'} < 0 .$$

Here $s$ is the probability that the lineage of a single cell growing at rates $(b, d)$ never dies out. The lesion is eradicated if and only if no type-$11$ lineage survives. With $k$ drugs the type space is $\{0,1\}^k$ and the construction is the same.

## Depends on

- [Limiting extinction probability in the supercritical case](../../../../Probability/branching-processes/linear-birth-death-process/tendsto-extinction-prob-of-lt.md)

## Expansion

For a linear birth–death process with rates $b > d$ started from one cell, the extinction probability $q$ solves $q = \frac{d}{b+d} + \frac{b}{b+d} q^2$, whose smaller root is $q = d/b$; hence the survival probability is $s = 1 - d/b$. Under treatment, sensitive lineages are subcritical ($b' < d'$) and die out almost surely, so failure requires a surviving fully resistant lineage, generated either before treatment (pre-existing resistance) or by mutation of the declining sensitive population during treatment. A fitness cost $c$ per resistance mutation can be added by letting a cell with $j$ resistance mutations divide at rate $(b - d)(1 - c)^j + d$.

## Sources

- I. Bozic, J. G. Reiter, B. Allen, T. Antal, K. Chatterjee, P. Shah, et al., "Evolutionary dynamics of cancer in response to targeted combination therapy", *eLife* 2 (2013), e00747, section "Materials and methods" (Model), <https://doi.org/10.7554/eLife.00747> (PMC3691570).
