# Many-loci limit and equilibria of genetic proximities

**Model.** $N$ monomorphic populations each carry a genome of $L$ loci; $A_{i,K}(t)$ is the allele of population $i$ at locus $K$. The genetic proximity is

$$P^L_{ij}(t)=\frac1L\sum_{K=1}^L\mathbf 1\{A_{i,K}(t)=A_{j,K}(t)\}.$$

At each locus, mutation at rate $\mu>0$ creates a new allele (infinite alleles), and migration from $i$ to $j$ copies the allele of $i$ onto $j$ at the effective rate $M_{ij}\,h(P^L_{ij}(t))$, where $M_{ij}\ge0$ ($M_{ii}=0$) are natural migration rates and the feedback $h:[0,1]\to[0,1]$ is continuous, nondecreasing, $h(0)=0$, $h(1)=1$ (gene flow fails between divergent populations).

**Many-loci limit.** As $L\to\infty$, $(P^L_{ij})$ converges in distribution to the solution of

$$\frac{dP_{ij}}{dt}=\sum_{k=1}^N\big(M_{ki}h(P_{ki})P_{kj}+M_{kj}h(P_{kj})P_{ki}\big)-P_{ij}\Big(\sum_{k=1}^N\big(M_{ki}h(P_{ki})+M_{kj}h(P_{kj})\big)+2\mu\Big),$$

with $P_{kk}=1$.

**Coalescent representation.** An equilibrium $P^{\rm eq}$ solves the fixed-point problem

$$P^{\rm eq}_{ij}=\mathbb E\big[e^{-2\mu\,T_{ij}(P^{\rm eq})}\big],$$

where $T_{ij}$ is the coalescence time of two ancestral lineages started at $i$ and $j$ that jump as random walks on the dual effective migration graph with rates $M_{ji}h(P^{\rm eq}_{ji})$: two populations share an allele iff their lineages coalesce before a mutation.

**Symmetric migration.** If $M_{ij}=m>0$ for all $i\ne j$, a symmetric equilibrium $P^{\rm eq}_{ij}=p$ solves

$$\varphi(p)=h(p)(1-p)-\frac\mu m\,p=0,$$

and it is locally stable iff $\varphi'(p)=h'(p)(1-p)-h(p)-\mu/m<0$. If $h'(0)=0$, stability of any equilibrium reduces to stability on each connected component of the dual effective migration graph. Asymmetric equilibria (two clusters with intercluster proximity, or intransitive "friendship" configurations) solve explicit three-dimensional systems.

## Depends on

- [Wright's island model](../../population-genetics/wright-s-island-model/README.md)

## Expansion

Each locus evolves as a Moran-type voter model with mutation on the effective migration graph, and the loci interact only through the proximities in the migration rates; averaging over $L$ loci gives a law of large numbers for $P^L$. Two-point moment equations of the voter model with mutation give the ODE: $P_{ij}$ increases when $i$ or $j$ copies from a $k$ that shares the other's allele, and decreases by copying from a $k$ that does not or by mutation. Large metapopulations favour the uniform coherent equilibrium, which is why larger species speciate less often.

## Sources

- A. Lambert, E. Schertzer, Y. Wenzel, "Geometry and stability of species complexes: larger species speciate less often", arXiv:2503.22784 (2025), Section 2 (model), Theorem 1, Theorem 9 (fixed point problem), Propositions 12–15, Section 7, <https://doi.org/10.48550/arXiv.2503.22784>.
