# Total one-step result of a STRIPS operator

For an operator with positive preconditions $P^+$, negative preconditions $P^-$, add set $A$ and delete set $D$, the result on a state $s$ is $(s \cup A) \setminus D$ when $P^+ \subseteq s$ and $P^-$ is disjoint from $s$, and $s$ otherwise (Bylander).
