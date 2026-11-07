# Kirchberger's theorem

Let $A$ and $B$ be finite sets of points in $\mathbb{R}^d$. Then $A$
and $B$ are strictly separated by a hyperplane, that is, there are a nonzero vector
$w \in \mathbb{R}^d$ and a real number $\beta$ with $\langle w, a \rangle < \beta$ for all $a \in A$
and $\beta < \langle w, c \rangle$ for all $c \in B$, if and only if for every set
$C \subseteq A \cup B$ of at most $d + 2$ points, the sets $A \cap C$ and $B \cap C$ are strictly
separated by a hyperplane in the same sense.

Proof: The reverse implication applies Helly's theorem to tagged strict half-spaces in one higher
dimension, following the route of Rademacher and Schoenberg (1950) from Kirchberger (1903).

## Sources

- https://en.wikipedia.org/wiki/Kirchberger%27s_theorem, statement `kirchberger-s1`.
- Paul Kirchberger, "Über Tchebychefsche Annäherungsmethoden," Mathematische Annalen 57 (1903), 509–540, DOI 10.1007/BF01445182, https://doi.org/10.1007/BF01445182.
