# Compiling preserves the execution relation

For every IMP command $c$, the relational denotation of its compiled diagram, with primitive blocks interpreted relationally and loops by finite-path feedback, equals the big-step execution relation of $c$. Equivalently, for all states $s$ and $t$, $(s, t)$ is in the relation of the compiled diagram if and only if $c$ runs from $s$ to $t$ in the big-step semantics: a morphism of the relational category is determined by its relation.
