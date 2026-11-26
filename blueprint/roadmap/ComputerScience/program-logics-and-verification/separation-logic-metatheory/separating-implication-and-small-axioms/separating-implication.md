# Separating implication

In Reynolds's model of separation logic a state is a pair of a *store* $s$, mapping variables to integers, and a *heap* $h$, a finite partial function from addresses to values. Heaps $h_0, h_1$ with disjoint domains are written $h_0 \perp h_1$, and $h_0 \cdot h_1$ is their union. Besides the formulas of predicate calculus, assertions include

- $\mathrm{emp}$, which holds when the heap is empty;
- $e \mapsto e'$, which holds when the heap has exactly one cell, at the address denoted by $e$, holding the value of $e'$;
- the *separating conjunction* $p_0 \ast p_1$, which holds in $(s, h)$ when $h = h_0 \cdot h_1$ for some $h_0 \perp h_1$ with $p_0$ true in $(s, h_0)$ and $p_1$ true in $(s, h_1)$;
- the *separating implication* $p_0 \mathrel{-\!\!\ast} p_1$, which holds in $(s, h)$ when for every heap $h'$ with $h' \perp h$ in which $p_0$ holds (with store $s$), $p_1$ holds in $(s, h \cdot h')$.

An assertion is *valid* if it holds in every state. For example, if $p$ holds for a store mapping $x$ to an address $\alpha$ and a heap mapping $\alpha$ to $16$, then $(x \mapsto 16) \mathrel{-\!\!\ast} p$ holds for the same store and that heap with $\alpha$ removed.

## Sources

- J. C. Reynolds, "Separation logic: a logic for shared mutable data structures", *Proceedings of the 17th Annual IEEE Symposium on Logic in Computer Science (LICS 2002)*, IEEE, 2002, author copy <https://www.cs.cmu.edu/~jcr/seplogic.pdf>, Sections 2 and 3.
