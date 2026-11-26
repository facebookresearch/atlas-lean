# Probability that a recombination leaves the local tree unchanged under the SMC'

Take a sample of size $n$ from a diploid population of constant effective size $N_e$, with time measured
in coalescent units of $2N_e$ generations. For a coalescent tree $\mathcal{T}$ let $T_i$ be the length of
the epoch with $i$ ancestral lineages, let

$$\sigma_i = T_n + T_{n-1} + \cdots + T_i \quad (i = 2,\dots,n), \qquad \sigma_{n+1} = 0,$$

let $A_n(t)$ be the right-continuous number of lineages ancestral to the sample at time $t$, and index the
$2n-2$ branches below the most recent common ancestor by $b$, with lower and upper endpoints $t_b^l$ and
$t_b^u$. Set

$$P_{ii} = -\frac1i e^{-i\sigma_i}, \qquad P_{ij} = \exp\Bigl(-i\sigma_i - \sum_{k=j+1}^{i-1} k T_k\Bigr)\frac1j\bigl(1 - e^{-jT_j}\bigr),$$

with an empty sum equal to $0$. Under the sequentially Markovian coalescent SMC', a recombination with
breakpoint on branch $b$ at time $t$ leaves the tree, meaning every coalescence time, unchanged with
probability

$$\mathbb{P}(\text{tree unchanged} \mid b,t,\mathcal{T}) = \frac1i + e^{it}\sum_{j = A_n(t_b^u)+1}^{i} P_{ij}, \qquad i = A_n(t).$$

Averaging the breakpoint uniformly along the branch,

$$\mathbb{P}(\text{tree unchanged} \mid b,\mathcal{T}) = \frac{1}{t_b^u - t_b^l}\sum_{i = A_n(t_b^u)+1}^{A_n(t_b^l)} p_b(i), \qquad
p_b(i) = \frac1i\Bigl[T_i + \bigl(e^{i\sigma_i} - e^{i\sigma_{i+1}}\bigr)\sum_{j = A_n(t_b^u)+1}^{i} P_{ij}\Bigr],$$

and weighting the branches by their lengths gives, with $L(\mathcal{T})$ the total branch length,

$$\mathbb{P}(\text{tree unchanged} \mid \mathcal{T}) = \frac{1}{L(\mathcal{T})}\sum_{b=1}^{2n-2} \sum_{i = A_n(t_b^u)+1}^{A_n(t_b^l)} p_b(i).$$

Under the SMC, where the detaching lineage may not reattach to the branch it left, this probability is
$0$.

## Depends on

- [Pairwise sequentially Markov coalescents SMC and SMC′](sequentially-markov-coalescent-smc-smc-pairwise.md)
- [Two-locus ancestral process for $n$ sequences](two-locus-ancestral-process-for-n-sequences.md)

## Proof depends on

- [Pairwise sequentially Markov coalescents SMC and SMC′](sequentially-markov-coalescent-smc-smc-pairwise.md)

## Expansion

Under the SMC' a recombination cuts a lineage at time $t$ on branch $b$ and the floating lineage
reattaches to any lineage available above $t$ at rate one per available lineage; the tree is unchanged
exactly when it reattaches to the same branch $b$ above the cut, that is before $t_b^u$. Integrating
$\exp\bigl(-\int_t^\tau A_n(s)\,ds\bigr)$, the probability of no earlier reattachment, over $\tau$ from
$t$ to $t_b^u$ and breaking the integral at the coalescence times $\sigma_j$ produces the coefficients
$P_{ij}$ and the term $1/i$ from the epoch containing $t$. The branch average is the uniform mixture over
the breakpoint position, and the tree-level statement is the law of total probability with the branch
chosen proportionally to its length, since recombination breakpoints fall on the tree at a rate
proportional to branch length.

## Sources

- Y. Deng, Y. S. Song and R. Nielsen, "The distribution of waiting distances in ancestral recombination graphs", Theoretical Population Biology 141 (2021), 34-43, <https://doi.org/10.1016/j.tpb.2021.06.003> (PMC8556732). (Propositions 1 and 2, Theorem 1.)
