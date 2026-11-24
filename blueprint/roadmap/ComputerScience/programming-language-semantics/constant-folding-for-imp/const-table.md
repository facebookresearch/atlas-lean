# Constant tables for IMP constant folding

A constant table is a function from variable indices to optional natural numbers, $t : \mathbb{N} \to \mathbb{N} \cup \{\bot\}$: $t(x) = n$ records that variable $x$ is known to hold the value $n$, and $t(x) = \bot$ records no known value.
