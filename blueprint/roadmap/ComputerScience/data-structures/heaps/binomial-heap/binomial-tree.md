# Binomial tree

A binomial tree over a type $\alpha$ is a node that stores a rank, which is
a natural number, a root value in $\alpha$, and a list of binomial trees over $\alpha$ as its
children. The type imposes no invariant; the binomial-tree shape and heap order are expressed
by a separate validity predicate.
