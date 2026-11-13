# Malécot's identity-by-descent model

Malécot's identity-by-descent model at one biallelic locus, at the level of second
moments. The individuals are `ι`; individual `i` carries the gene copies `(i, 0)` (paternal) and
`(i, 1)` (maternal), and `allele c ∈ {0, 1}` indicates the reference allele on copy `c`. The
reference allele has frequency `p ∈ (0, 1)` (a polymorphic locus), and `ibd c d` is the
probability that the copies `c` and `d` are identical by descent: IBD copies carry the same
allele and non-IBD copies are independent draws with frequency `p` (Malécot 1948), which gives
the second moments `𝔼[a_c a_d] = p² + p (1 - p) ibd c d`. Only these first and second moments
are assumed. `ibd` is determined by the moments (`p (1 - p) ≠ 0`), and `ibd c c = 1`
(`IBDModel.ibd_self`). In Malécot's model `ibd c d ∈ [0, 1]`; the structure does not require
this, and the identities below hold for any real `ibd` (for example a correlation relative to a
reference population, which can be negative). A monomorphic locus (`p ∈ {0, 1}`) is excluded:
there the GRM denominator `2p(1 - p)` vanishes.
