# Path-space limits of Cannings ancestral partitions to Λ-coalescents

This page covers a research target: convergence in law, in the Skorokhod space of paths of partitions, of the rescaled ancestral partition processes of [Cannings models](../cannings-models/cannings-model.md) to the Λ-coalescent, under the Möhle–Sagitov conditions for a Λ-coalescent limit.

The block counts already converge, by [the Möhle–Sagitov limit of the lineage count](tendsto-lineage-matrix-pow.md), and for a fixed sample the transition matrices of the partition chain converge by [the fixed-sample partition limit](mohle-sagitov-fixed-n-cannings-partition-generat.md). The residual target is the path-level statement. In the Kingman case it is [the path-level convergence in Skorokhod space](../kingman-limit-of-cannings-models/path-level-convergence-of-rescaled-ancestral-par.md).

## Expansion

State the path-space convergence for a fixed sample size, with the hypotheses fixed from a source, and prove it from the finite-dimensional limit and a tightness argument adapted to multiple mergers.

Prerequisites:

- [Convergence of Cannings ancestral partition chains for a fixed sample size](mohle-sagitov-fixed-n-cannings-partition-generat.md)
- [Möhle–Sagitov limit of the lineage count of Cannings models](tendsto-lineage-matrix-pow.md)
- [Path-level convergence of rescaled ancestral partition chains in Skorokhod space](../kingman-limit-of-cannings-models/path-level-convergence-of-rescaled-ancestral-par.md)

## Sources

- M. Möhle and S. Sagitov, A classification of coalescent processes for haploid exchangeable population models, *Ann. Probab.* 29 (2001), 1547–1562, <https://doi.org/10.1214/aop/1015345761>.
- S. Sagitov, The general coalescent with asynchronous mergers of ancestral lines, *J. Appl. Probab.* 36 (1999), 1116–1125.
