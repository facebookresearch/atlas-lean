# Unguarded output in a process

A π-calculus process has an unguarded output when an output occurs in it not behind a prefix, on any subject (bound names included). Recursively: $\mathbf{0}$ and every input $a(\cdot).P$ have none, every output $\bar{a}\langle b\rangle.P$ has one, $P \mid Q$ and $P + Q$ have one when $P$ or $Q$ has one, and $\nu P$ and $!P$ have one when $P$ has one. This overapproximates the outputs that can take part in a communication, since an output in a branch of a choice counts; it is not a barb.
