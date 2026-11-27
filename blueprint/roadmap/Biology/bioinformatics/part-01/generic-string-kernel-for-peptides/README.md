# Generic string kernel for peptides

A string kernel for short amino-acid sequences that compares all pairs of substrings up to length $L$ through physico-chemical encodings of residues, with a Gaussian penalty on the shift between their positions. It contains the oligo, weighted-degree, blended-spectrum and RBF kernels as limiting cases and is used with kernel ridge regression to predict peptide–protein binding affinities.

- [Positive semi-definiteness of the generic string kernel](positive-semi-definiteness-of-the-generic-string-kernel.md)
