# Sequential composition is relational composition

For IMP commands $c$ and $d$, the [execution relation](command-rel.md) of $c; d$ is the composite, in the relation category of IMP states, of the execution relation of $c$ followed by that of $d$. Pointwise: $c; d$ executes from $s$ to $t$ if and only if there is a state $m$ such that $c$ executes from $s$ to $m$ and $d$ executes from $m$ to $t$. The two readings convert into each other by evaluating the morphism equality at a pair of states and, conversely, by extensionality of relations.
