# One round of the attribute-closure algorithm

For a finite set $F$ of functional
dependencies and a finite set $Y$ of attributes, one closure round returns $Y$ together with the
right side of every dependency of $F$ whose left side is contained in $Y$, that is, the set
$Y \cup \bigcup \{R : (L \to R) \in F,\ L \subseteq Y\}$.
