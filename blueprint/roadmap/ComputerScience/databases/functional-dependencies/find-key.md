# Key-finding algorithm

Let $F$ be a finite set of functional dependencies on a finite set
of attributes $A$, and let $l$ be a list of attributes. The key-finding algorithm starts from the
set $K = A$ of all attributes and goes through $l$ in order: for each listed attribute $a$, it
replaces $K$ by $K \setminus \{a\}$ when the attribute closure of $K \setminus \{a\}$ under $F$ is
all of $A$, and keeps $K$ otherwise. It returns the final set $K$.
