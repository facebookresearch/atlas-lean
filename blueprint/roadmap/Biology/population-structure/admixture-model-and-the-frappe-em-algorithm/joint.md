# Joint weight of an allele copy and its ancestral population

For [admixture parameters](params.md) $\theta = (Q, F)$, an allele-copy observation $(i, j, a)$ with $a$ true when the copy carries the reference allele, and a population $k \in K$, the joint weight is

$$p_\theta((i, j, a), k) = Q_{ik} \cdot \begin{cases} F_{kj} & a \text{ true},\\ 1 - F_{kj} & a \text{ false}. \end{cases}$$
