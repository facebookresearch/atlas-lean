# RNA secondary structure

A secondary structure on `s` (Nussinov et al. 1978): a finite set of base pairs `(i, j)`,
each closing a hairpin with at least `m` unpaired positions strictly inside (`i + m < j`), joining
complementary bases (`pair s[i] s[j]`, which also puts both positions inside `s`), with every
position in at most one pair and no two pairs crossing (`i < k < j < l`).
