# Droplet single-cell barcoding

Droplet methods for single-cell RNA sequencing encapsulate cells with barcoded beads in emulsion partitions, so that every read carries a cell barcode and a unique molecular identifier (UMI). Two pieces of mathematics govern the data: Poisson loading of cells into partitions, which sets the multiplet rate, and Bayesian correction of sequencing errors in barcodes.

- [Barnyard estimator of the multiplet rate](barnyard-estimator-of-the-multiplet-rate.md)
- [Posterior correction of cell barcodes at Hamming distance one](posterior-correction-of-cell-barcodes-at-hamming-distance-one.md)
