# Plate effects in single-cell differential expression

In plate- or chip-based single-cell RNA sequencing, all cells on a plate usually come from one population of one biological group, so gene-specific plate effects are confounded with the groups being compared. Treating cells as independent replicates then ignores the positive correlation induced by the shared plate effect and inflates the type I error; summing counts within plates restores independent replicates.

- [Plate-effect model and summation over cells](plate-effect-model-and-summation-over-cells.md)
