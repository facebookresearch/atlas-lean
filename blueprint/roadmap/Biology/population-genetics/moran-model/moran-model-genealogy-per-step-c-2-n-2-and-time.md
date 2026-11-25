# Neutral Moran genealogy as a relabeled Cannings model

Fix an integer $N\ge2$. In each **neutral** Moran step choose a uniform
reproducer $R$ and, independently, a uniform replaced individual $J$.
Allow $R=J$. The parent map is $f(J)=R$ and $f(i)=i$ for $i\ne J$.
Take independent choices at successive steps.
This literal map law is not child-permutation invariant: the identity
has mass $1/N$, while any nonidentity permutation, in particular a
transposition, has mass zero.

Let $\sigma,\tau$ be independent uniform permutations of child and
parent labels, independent of $f$, and replace it by
$\widetilde f=\tau\circ f\circ\sigma$ independently at each step.
This law is invariant under either permutation action and hence is a
[Cannings model](../../coalescent-theory/multiple-merger-coalescents/cannings-models/cannings-model.md).
Its unlabelled ancestral partition process has exactly the same law as
the literal neutral Moran process, for a fixed sample of distinct
individuals. This assertion concerns sample partitions, not equality
of the individual-label trajectories.

For either encoding the factorial moments and pair probability are

$$\mu_2=\frac{2(N-1)}{N^2},\qquad\mu_3=0,
\qquad c_N=\frac{\mu_2}{N-1}=\frac2{N^2}.$$

Thus the [Möhle–Sagitov conditions](../../coalescent-theory/multiple-merger-coalescents/kingman-limit-of-cannings-models/mohle-sagitov.md)
hold for the relabeled family, with the trivial laws at $N=0,1$.
For a fixed sample size, both encodings converge in finite-dimensional
distributions to Kingman's genealogy at times $\lfloor tN^2/2\rfloor$
Moran steps. With the explicit convention of $N$ Moran steps per
generation, the clock is $N/2$ generations, half the neutral
[Wright–Fisher clock](../../coalescent-theory/multiple-merger-coalescents/kingman-limit-of-cannings-models/wright-fisher-as-a-cannings-model-satisfying-moh.md)
for the same number of gene copies. Excluding self-replacement or
introducing selection changes this model and is not covered implicitly.

## Depends on

- [Cannings parent-map law](../../coalescent-theory/multiple-merger-coalescents/cannings-models/cannings-model.md)
- [Möhle–Sagitov conditions](../../coalescent-theory/multiple-merger-coalescents/kingman-limit-of-cannings-models/mohle-sagitov.md)

## Proof depends on

- [Canonical finite-dimensional Kingman limit](../../coalescent-theory/multiple-merger-coalescents/kingman-limit-of-cannings-models/tendsto-chain-fdd.md)

## Background

- [Moran allele-count matrix, specialized to relative fitness one](moran-matrix.md)

## Expansion

When $R=J$ all offspring numbers equal one. Otherwise exactly one
parent has two offspring, one has none and the remainder have one.
For a fixed parent, the probability of two offspring is
$(N-1)/N^2$, proving the moments and the absence of triples or simultaneous
separate pair mergers. Uniformity of $\sigma$ absorbs every extra child
permutation, and uniformity of $\tau$ absorbs every extra parent
permutation, proving both Cannings invariances.

For the full relabeling claim, condition on the entire genealogy traced
so far. Suppose its $b\le N$ current sample blocks occupy distinct
individual labels $a_1,\ldots,a_b$. The next literal parent map merges
one specified unordered pair of blocks $u,v$ exactly when
$(J,R)=(a_u,a_v)$ or $(a_v,a_u)$, a probability $2/N^2$.
No other merger pattern can occur. Therefore its partition kernel has
probability $2/N^2$ for each specified pair merger and
$1-b(b-1)/N^2$ for no change, independently of the actual labels.
Precomposing by $\sigma$ merely changes the distinct labels to which
this same calculation applies; postcomposing by $\tau$ preserves all
parent equalities. Thus the conditional partition kernel is identical
for both encodings after every history. Starting from the same sample
partition, induction gives equality of every finite-time joint law,
hence of the discrete-time partition-process laws.
In particular their lineage-count kernels agree: row $b$ has mass
$b(b-1)/N^2$ at $b-1$ and the remaining mass at $b$.
Apply the linked limit theorem to the relabeled chain, then transfer its
finite-dimensional limit through this exact kernel equality.

## Sources

- M. Möhle and S. Sagitov, "A classification of coalescent processes for haploid exchangeable population models", Annals of Probability 29 (2001), 1547–1562, <https://doi.org/10.1214/aop/1015345761>. The moments are computed above.
