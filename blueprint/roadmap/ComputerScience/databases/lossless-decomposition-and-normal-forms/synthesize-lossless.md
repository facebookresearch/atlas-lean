# Synthesis is lossless

Let $A$ be a finite set of attributes, $D$ a type of values, $F$ a finite set of functional
dependencies over $A$, $G$ a list of functional dependencies equivalent to $F$ (each derives every
dependency of the other), and $K$ a superkey for $F$. Then every relation $r$ over all of $A$ (each
tuple defined on every attribute) that satisfies every dependency of $F$ is the natural join of
its projections onto the schemes of the decomposition synthesized from $G$ and $K$, namely $K$
and the scheme $X \cup Y$ for each dependency $X \to Y$ of $G$.
