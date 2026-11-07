# Pedigree

A pedigree on the individuals `Fin n`, numbered so that parents precede their children
(every finite pedigree, a finite DAG, has such a numbering). `parents i = some g` means that
`g 0` is the father and `g 1` the mother of `i`; `parents i = none` means that `i` is a founder.
Founders are unrelated and not inbred (their `2 n_F` gene copies are distinct).
