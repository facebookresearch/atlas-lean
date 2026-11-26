# Cell-probe execution results

A cell-probe execution result contains the value of type `α` at the reached return leaf, the
final memory (still a map `Fin cells → BitVec width`), and a natural-number count of read and
write occurrences on the execution path, including repeated probes.
