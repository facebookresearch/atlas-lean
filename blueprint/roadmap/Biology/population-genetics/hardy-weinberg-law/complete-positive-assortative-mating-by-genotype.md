# Complete positive assortative mating with equal genotype-class contribution

Use a deterministic biallelic population with genotype frequencies
$P_t,H_t,Q_t\ge0$, $P_t+H_t+Q_t=1$, for $AA,Aa,aa$.
Specify the mating-pair law to give the pairs
$(AA,AA),(Aa,Aa),(aa,aa)$ probabilities $P_t,H_t,Q_t$, respectively,
and all other pairs probability zero. Thus every genotype class contributes
in proportion to its frequency, not in proportion to its squared frequency.
All pairs have the same expected offspring number, gametes segregate by
[Mendel's law](transmit.md), and the two gametes of a
pair are independent. There is no mutation, selection or drift beyond this
specified mating rule.

Then

$$H_{t+1}=H_t/2,\qquad P_{t+1}=P_t+H_t/4,\qquad
 Q_{t+1}=Q_t+H_t/4.$$

Indeed the two homozygous crosses breed true and $Aa\times Aa$ gives the
proportions $1/4:1/2:1/4$. These recursions preserve nonnegativity and total
mass, and $p=P_t+H_t/2$ is constant. Consequently

$$H_t=2^{-t}H_0,\quad P_t=p-2^{-t}H_0/2,\quad
 Q_t=1-p-2^{-t}H_0/2,$$

so the genotype law converges to $p\,\delta_{AA}+(1-p)\delta_{aa}$.
The genotype-frequency recursion is the same as complete selfing; this does
not identify the two pedigrees or their identity-by-descent relations.

## Depends on

- [Mendelian transmission](transmit.md)

## Expansion

Merely requiring same-genotype pairs and equal fertility per successful
mating does not fix their class weights. For example, drawing two independent
parents and conditioning on equal genotypes weights the three allowed pairs
proportionally to $P_t^2,H_t^2,Q_t^2$, a different model. Assortment by
phenotype when $AA$ and $Aa$ are indistinguishable is also excluded.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, V.1, p. 217, for the distinction between assortment and inbreeding. The explicitly class-balanced mating law and its recursion are derived here; that introductory paragraph is not represented as a theorem for every assortment mechanism.
