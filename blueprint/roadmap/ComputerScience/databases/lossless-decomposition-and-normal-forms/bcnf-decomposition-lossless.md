# The BCNF decomposition is lossless

Let $F$ be a set of functional dependencies, $l$ a list
of attributes and $S$ a set of attributes, and let $r$ be a relation over $S$ that satisfies every
dependency $X \to Y$ derivable from $F$ with $X, Y \subseteq S$. Then $r$ is the natural join of
its projections onto the schemes of the BCNF decomposition of $S$ for $F$ and $l$.
