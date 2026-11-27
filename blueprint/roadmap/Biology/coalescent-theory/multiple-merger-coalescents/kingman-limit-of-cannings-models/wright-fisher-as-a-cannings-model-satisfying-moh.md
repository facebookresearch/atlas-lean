# Wright–Fisher as a Cannings model with clock N generations

For an integer $N\ge2$, independently assign each of $N$ children a
uniform parent in $\{0,\ldots,N-1\}$. Thus every parent map $f$ has mass
$N^{-N}$. This law is invariant under precomposition by a child
permutation and postcomposition by a parent permutation, so it defines
the canonical [Cannings model](../cannings-models/cannings-model.md).
Use independent copies of the parent map in successive generations.

For any parent, the offspring number $\nu$ is
$\operatorname{Binomial}(N,1/N)$. Its falling-factorial moments are

$$\mu_2=\frac{N(N-1)}{N^2},\qquad
\mu_3=\frac{N(N-1)(N-2)}{N^3}.$$

Consequently the canonical [pair probability](pair-coalescence.md) and
third-moment ratio are

$$c_N=\frac{\mu_2}{N-1}=\frac1N,\qquad
\frac{\mu_3}{N^2c_N}=\frac{(N-1)(N-2)}{N^3}\le\frac1N.$$

In particular $c_N>0$, $c_N\to0$ and the ratio tends to zero, proving
the [Möhle–Sagitov conditions](mohle-sagitov.md).
For every fixed sample size $n$, the ancestral partitions observed at
$\lfloor tN\rfloor$ generations converge in finite-dimensional
distributions to Kingman's $n$-coalescent. The clock is $N$ generations;
for a diploid Wright–Fisher population with $2N_d$ gene copies it is
$2N_d$ generations. No path-space convergence claim is added here.

For $n\le N$, the Cannings lineage-count matrix equals the
[Wright–Fisher lineage-count matrix](../../ancestral-lineage-counting-and-tavar-s-formula/wf-lineage-matrix.md).
In a row with $b\le n$, its entry for $a$ parents is
$S(b,a)(N)_a/N^b$, where $S(b,a)$ is a Stirling number of the second kind.
The sample-size gate matters: the Cannings coalescence matrix has zero rows for $b>N$,
whereas the unrestricted occupancy formula need not do so.

## Depends on

- [Cannings parent-map law](../cannings-models/cannings-model.md)
- [Möhle–Sagitov conditions](mohle-sagitov.md)
- [Offspring factorial moments](factorial-moment.md)
- [Pair-coalescence probability](pair-coalescence.md)

## Proof depends on

- [Canonical finite-dimensional Kingman limit](tendsto-chain-fdd.md)

## Background

- [Forward Wright–Fisher allele-count kernel](../../../population-genetics/wright-fisher-markov-chain/wright-fisher.md)
- [Wright–Fisher occupancy probabilities](../../ancestral-lineage-counting-and-tavar-s-formula/wf-lineage-prob.md)

## Expansion

Both permutation actions are bijections of the finite set of parent
maps, proving the two law invariances. To compute $\mathbb E(\nu)_k$,
sum indicators over ordered $k$-tuples of distinct children: each tuple
chooses the specified parent with probability $N^{-k}$. This gives
$(N)_k/N^k$. For $b$ distinct sampled children, a specified partition into
$a$ parental groups has $(N)_a$ injective assignments of parents and
each assignment has probability $N^{-b}$; summing over $S(b,a)$ such
partitions gives the lineage matrix identity. This is an instance of
the occupancy and Cannings definitions, not a new model.
Extend the family at $N=0,1$ by the unique empty/singleton parent-map
laws; the canonical pair probabilities there are zero, not $1/N$.
Those finite exceptions do not affect the asymptotic conditions or the
fixed-$n$ limit, where $N\ge n$ eventually. Apply the linked Cannings
finite-dimensional convergence theorem with $1/c_N=N$.

## Sources

- M. Möhle and S. Sagitov, "A classification of coalescent processes for haploid exchangeable population models", Annals of Probability 29 (2001), 1547–1562, <https://doi.org/10.1214/aop/1015345761>. The moments are computed above.
