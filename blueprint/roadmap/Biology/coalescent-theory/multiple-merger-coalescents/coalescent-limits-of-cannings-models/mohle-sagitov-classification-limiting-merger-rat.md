# Möhle–Sagitov classification of the coalescent limits of Cannings models

This page covers a research programme: the classification of the limits of the ancestral processes of [Cannings models](../cannings-models/cannings-model.md) as Ξ-coalescents.

1. **Raw-moment hypothesis.** $c_N \to 0$ and, for all $a \ge 1$ and $k_1, \dots, k_a \ge 2$,

$$\frac{\mathbb{E}\bigl[(\nu_1)_{k_1} \cdots (\nu_a)_{k_a}\bigr]}{N^{k_1 + \cdots + k_a - a}\, c_N} \to \phi_a(k_1, \dots, k_a),$$

where $\nu$ is the offspring vector and $(x)_k$ the falling factorial.

2. **From moments to rates.** The limits $\phi$ determine the pattern limits $q$ of [the generator convergence lemma](generator-convergence-of-cannings-partition-chai.md) by inclusion–exclusion over singleton factors. The raw $\phi$ are not transition rates. In the sweepstake model $\phi_1(2) = 1$ but the rate of a binary merger among three lineages is $0$.

3. **Representation.** The limiting rates are those of a [Ξ-coalescent](../../coalescents/xi-coalescent-partition-valued-ctmc-and-restrict.md) for a unique finite measure $\Xi$ on the infinite simplex, through the moment problem on the simplex. This gives the trichotomy: Kingman's coalescent, a Λ-coalescent when simultaneous multiple mergers vanish in the limit, or a general Ξ-coalescent.

## Expansion

Split the programme into separately stated results, each with hypotheses fixed from a source:

1. The transform from $\phi$ to $q$, under the hypothesis of [the fixed-sample convergence theorem](mohle-sagitov-fixed-n-cannings-partition-generat.md).
2. The representation of the limit rates by a unique finite $\Xi$.
3. The reduction to a Λ-coalescent when simultaneous multiple mergers vanish, and to Kingman's coalescent when, in addition, triple mergers vanish.

Prerequisites:

- [Convergence of Cannings ancestral partition chains for a fixed sample size](mohle-sagitov-fixed-n-cannings-partition-generat.md)
- [The Ξ-coalescent rate matrix on partitions of a finite sample](../../coalescents/xi-coalescent-partition-valued-ctmc-and-restrict.md)

## Sources

- M. Möhle and S. Sagitov, A classification of coalescent processes for haploid exchangeable population models, *Ann. Probab.* 29 (2001), 1547–1562, <https://doi.org/10.1214/aop/1015345761> (classification theorem).
- J. Schweinsberg, Coalescents with simultaneous multiple collisions, *Electron. J. Probab.* 5 (2000), paper 12, <https://doi.org/10.1214/EJP.v5-68> (Ξ rates).
