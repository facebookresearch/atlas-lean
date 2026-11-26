# Running a generic-group program with a fixed encoding

Let `1 < q` and `enc` a permutation of `ZMod q` encoding group elements as
labels. `runProg enc inputs p` compiles the generic-group program `p` into an
oracle computation and runs it against the oracle of `enc` on the input
labels. Only program syntax is accepted, so a literal label cannot be
supplied.
