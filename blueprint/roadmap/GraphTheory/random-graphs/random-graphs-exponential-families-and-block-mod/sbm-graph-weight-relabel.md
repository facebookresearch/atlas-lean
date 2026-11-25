# Sbm Graph Weight relabel

Assume that `V` is finite and that `K` is finite.

Label swapping (Allman, Matias and Rhodes 2009, Section 2): relabeled parameters give the
same weight.

Parameters are identified at most modulo permutation of the classes: a
numerical clustering output is not statistical identification. Under
`SBMAdmissible` this is equality of laws (see `sbmGraphPMF_relabel`).
