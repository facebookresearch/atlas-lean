# The key-finding algorithm returns a candidate key

Let $F$ be a finite set of functional
dependencies on a finite set of attributes $A$, and let $l$ be a list in which every attribute
of $A$ occurs. Then the output of the key-finding algorithm on $F$ and $l$, which starts from the
set of all attributes and goes through $l$ in order, removing each listed attribute whenever
what remains is still a superkey, is a candidate key for $F$.
