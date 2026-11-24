# Preorder walk with an accumulator

For a forest $F$ and a list $a$ of vertices, this is the
timed computation defined as follows. On the empty forest it returns $a$ at no cost. On a forest
with first root $v$, children forest $C$ and sibling forest $S$, it charges one time unit, walks
$S$ with accumulator $a$ to get a list $b$, walks $C$ with accumulator $b$ to get a list $c$, and
returns $v$ followed by $c$. It thus returns the vertices of $F$ in preorder followed by $a$, at
one time unit per vertex of $F$.

The accumulator means no list is ever appended, so the untimed work is linear as well.
