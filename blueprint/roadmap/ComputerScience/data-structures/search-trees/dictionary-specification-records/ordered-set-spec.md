# Ordered Set Spec

A finite ordered-set implementation over a linearly ordered key type: states with an empty state, insertion, deletion, a membership predicate, a validity invariant and an abstraction to finite sets of keys, such that the empty state is valid and abstracts to $\emptyset$; insertion and deletion preserve validity; on a valid state, inserting $x$ abstracts to the abstraction with $x$ added and deleting $x$ to the abstraction with $x$ removed; and on a valid state, membership of $x$ is equivalent to $x$ lying in the abstraction.
