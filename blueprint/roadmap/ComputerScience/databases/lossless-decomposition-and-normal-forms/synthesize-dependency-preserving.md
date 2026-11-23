# Synthesis is dependency-preserving

Let $F$ be a finite set of functional dependencies and
$G$ a list of functional dependencies equivalent to $F$ (each derives every dependency of the
other). Then for every set of attributes $K$, the decomposition synthesized from $G$ and $K$,
with one scheme $X \cup Y$ for each dependency $X \to Y$ of $G$ together with the scheme $K$, is
dependency-preserving for $F$.
