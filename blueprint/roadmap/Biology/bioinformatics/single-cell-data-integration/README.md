# Single-cell data integration

Integrating single-cell datasets means removing dataset- or batch-specific variation from a shared low-dimensional embedding while keeping cell-type structure. These articles state the two alternating steps of the Harmony algorithm: a soft clustering that penalizes clusters dominated by one batch, and a cluster-wise linear mixture-of-experts regression that subtracts batch effects.

- [Maximum-diversity soft clustering](maximum-diversity-soft-clustering.md)
- [Mixture-of-experts batch correction](mixture-of-experts-batch-correction.md)
