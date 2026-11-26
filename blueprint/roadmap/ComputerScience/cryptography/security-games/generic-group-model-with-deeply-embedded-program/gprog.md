# Generic-group programs

Deeply embedded generic programs over `n` labels addressed by `Fin` indices.
`ret i` returns the `i`-th label; `mul i j k` and `inv i k` issue one oracle
query over the indexed labels and run the continuation `k` with the answer
bound at a fresh index; `eqTest i j kt kf` runs `kt` or `kf` depending on
whether the indexed labels agree. A program mentions labels only through
indices: no constructor holds a label value, so a program can neither inspect
nor synthesize label representations. Indices address the labels received so
far, the inputs first and then the oracle answers in order; the continuation
of `mul` or `inv` sees the answer at index `Fin.last _` and earlier labels
through `Fin.castSucc`.
