# Shrinking a key along a list

Let $F$ be a finite set of functional dependencies over a
finite set of attributes. Given a list $l$ of attributes and a set of attributes $K$, go through
$l$ in order and, for each attribute $a$, remove $a$ from the current set whenever the attribute
closure under $F$ of the current set without $a$ is the set of all attributes (that is, the set
without $a$ is still a superkey); the result is the set reached at the end of the list.
