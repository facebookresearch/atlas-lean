# Count Model

A count-matrix observation model for genes `G`, samples `J` and conditions `C`. Sample `j` is
a biological replicate of condition `condition j` with library size (size factor)
`librarySize j`; gene `g` has the count law `law g` and normalized expression `rate g c` in
condition `c`. The count of gene `g` in sample `j` has law `(law g).pmf (mean g j)` with mean
`librarySize j * rate g (condition j)`.
