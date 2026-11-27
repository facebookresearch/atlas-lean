# Armstrong's theorem

Let $A$ be a finite set of attributes, $F$ a finite set of
functional dependencies over $A$ and $f$ a functional dependency over $A$. Then $f$ is
derivable from $F$ with Armstrong's axioms if and only if $F$ entails $f$, that is, $f$ holds
in every relation (with values in any type) that satisfies every dependency of $F$. In other
words, Armstrong's axioms are sound and complete for functional dependencies.
