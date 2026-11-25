# Populations related by a tree without migration have f4 = 0 for sister pairs

Let populations $A, B, C, D$ be related by a rooted population tree with no migration, in which $A$ and $B$ descend from a population $AB$ that splits
at time $\tau_{AB}$, before either lineage can meet a lineage from $C$ or $D$. Sample one gene from each population and let $T(X, Y)$ be the expected
coalescence time of the genes from $X$ and $Y$. A gene from $A$ cannot coalesce with a gene from $C$ before both are in a common ancestral
population, which happens after $\tau_{AB}$. At $\tau_{AB}$ the gene from $A$ enters $AB$, and from then on its ancestral path has the same law
as that of a gene from $B$ entering $AB$ at $\tau_{AB}$. Hence the coalescence time of the genes from $A$ and $C$ has the same law as that of the genes
from $B$ and $C$, so $T(A, C) = T(B, C)$, and likewise $T(A, D) = T(B, D)$. In a [coalescent model](coalescent-model.md) with these times, the [coalescent form of $f_4$](f4-eq.md) gives

$$f_4(A, B; C, D) = \frac\theta2 \bigl(T(A, D) + T(B, C) - T(A, C) - T(B, D)\bigr) = 0 .$$

For example, if every ancestral population coalesces pairs at rate $1$ (time in units of $2N$ generations) and the tree is
$((A, B), (C, D))$ with split times $\tau_{AB}, \tau_{CD} < \tau_R$, then $T(A, B) = \tau_{AB} + 1$, $T(C, D) = \tau_{CD} + 1$ and the four cross times equal
$\tau_R + 1$, so $f_4(A, B; C, D) = 0$, while the coalescent form gives $f_4(A, C; B, D) = \frac\theta2 (2\tau_R - \tau_{AB} - \tau_{CD}) > 0$.

## Depends on

- [Coalescent model linking heterozygosity and coalescence times](coalescent-model.md)

## Proof depends on

- [$f_4$ in terms of expected coalescence times](f4-eq.md)

## Sources

- N. Patterson et al., "Ancient admixture in human history", Genetics 192 (2012), 1065–1093, <https://doi.org/10.1534/genetics.112.145037>. The equalities are derived above.
