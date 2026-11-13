# Gene-expression deconvolution

Write the bulk matrix (genes × samples) as `C * P`, the
cell-type profiles `C` times the cell-type proportions `P`. If the proportions of sample `j` are
nonnegative and sum to `1` and every cell type expresses gene `g` at a level in `[lo, hi]`, then
the bulk level of `g` in sample `j` lies in `[lo, hi]`.
