# Candidate keys are the superkeys minimal under single removals

Let $F$ be a finite set
of functional dependencies on a finite set of attributes $A$. A set $K \subseteq A$ of attributes
is a candidate key for $F$ if and only if $K$ is a superkey for $F$ and, for every $a \in K$, the
set $K \setminus \{a\}$ is not a superkey for $F$.
