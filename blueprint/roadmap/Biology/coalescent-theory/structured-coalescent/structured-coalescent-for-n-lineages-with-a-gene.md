# Structured coalescent for n lineages with a general migration matrix

Let there be $d$ demes with relative sizes $c_1, \dots, c_d > 0$ and raw per-generation backward migration probabilities $q_{ij} \ge 0$, $i \ne j$. With $M$ the number of gene copies in the reference population, set the scaled parameters $m_{ij} = 2M q_{ij}$. In time units of $M$ generations:

- each lineage moves from deme $i$ to deme $j$ at rate $m_{ij}/2 = M q_{ij}$;
- each pair of lineages in deme $i$ coalesces at rate $1/c_i$.

The structured coalescent of $n$ lineages is the continuous-time Markov chain with these rates on partitions of $[n]$ whose blocks carry deme labels. It lumps to the chain of the numbers of lineages in each deme. Eventual coalescence needs the migration to be irreducible.

In the island model, $q_{ij} = m/(d - 1)$ for $i \ne j$; then $M_{\mathrm{mig}} = 4Nm = 2Mm$ for $N$ diploid individuals, each lineage migrates to each other deme at rate $M_{\mathrm{mig}}/(2(d - 1))$, and its total migration rate is $M_{\mathrm{mig}}/2$, as in [the island model's mean coalescence times](mean-coalescence-time.md).

## Depends on

- [Closed-form mean coalescence times in the island model](mean-coalescence-time.md)

## Proof depends on

- [Rate matrix of Kingman's partition-valued coalescent](../partition-valued-kingman-coalescent/partition-rate.md)

## Expansion

1. The rate matrix on deme-labelled partitions and its lumping to deme counts.
2. Checks: $d = 1$ recovers [the rate matrix of Kingman's partition-valued coalescent](../partition-valued-kingman-coalescent/partition-rate.md). Two lineages in the symmetric island model recover the pair-state rates of [the island model](mean-coalescence-time.md). The island specialization of the per-lineage rate is $M_{\mathrm{mig}}/(2(d - 1))$ to each other deme.

## Sources

- M. Notohara, The coalescent and the genealogical process in geographically structured population, *J. Math. Biol.* 29 (1990), 59–75, <https://pubmed.ncbi.nlm.nih.gov/2277236/> (general structured coalescent).
- J. Wakeley, *Coalescent Theory: An Introduction*, Roberts and Company (2009), Chapter 5.
