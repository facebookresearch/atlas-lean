# States on infinite paths are safe under k-induction

Let $\to$ be a binary relation on a type $S$, and call a sequence $(p_i)_{i \in \mathbb{N}}$ an infinite path when $p_i \to p_{i+1}$ for every $i$. Let $\mathrm{Init}$ and $\mathrm{Bad}$ be predicates on $S$ and $k \in \mathbb{N}$. Assume the base case: for every infinite path $(p_i)$ with $\mathrm{Init}(p_0)$, $\mathrm{Bad}(p_i)$ fails for every $i < k$; and the step case: for every infinite path $(p_i)$ such that $\mathrm{Bad}(p_i)$ fails for every $i < k$, $\mathrm{Bad}(p_k)$ fails. Then every state $s$ that occurs on some infinite path from an initial state (that is, $s = p_i$ for some $i$ and some infinite path $(p_i)$ with $\mathrm{Init}(p_0)$) satisfies: $\mathrm{Bad}(s)$ fails.

A state that lies on no infinite path from an initial state is not covered.

## Sources

- M. Sheeran, S. Singh and G. Stålmarck, *Checking safety properties using induction and a SAT-solver*, Formal Methods in Computer-Aided Design (FMCAD 2000), LNCS 1954, Springer, 2000, pp. 108–125.
