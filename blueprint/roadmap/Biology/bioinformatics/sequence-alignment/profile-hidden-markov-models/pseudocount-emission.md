# Pseudocount emission estimate of a match state

The emission estimate of a match state from the residues `col` that a multiple alignment
places in its column (gaps omitted), with pseudocounts `pc` (Durbin et al., chapter 5;
Laplace's rule is `pc = 1`): `(count a + pc a) / (|col| + ∑ b, pc b)`.
