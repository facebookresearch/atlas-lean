# Soundness of k-induction along infinite paths

Let $\to$ be a binary relation on a type $S$, and call a sequence $(p_i)_{i \in \mathbb{N}}$ an infinite path when $p_i \to p_{i+1}$ for every $i$. Let $\mathrm{Init}$ and $\mathrm{Bad}$ be predicates on $S$ and $k \in \mathbb{N}$. Assume the base case: for every infinite path $(p_i)$ with $\mathrm{Init}(p_0)$, $\mathrm{Bad}(p_i)$ fails for every $i < k$; and the step case: for every infinite path $(p_i)$ such that $\mathrm{Bad}(p_i)$ fails for every $i < k$, $\mathrm{Bad}(p_k)$ fails. Then for every infinite path $(p_i)$ with $\mathrm{Init}(p_0)$, $\mathrm{Bad}(p_i)$ fails for every $i \in \mathbb{N}$.

Equivalently, every state $s$ that occurs on some infinite path from an initial state (that is, $s = p_i$ for some $i$ and some infinite path $(p_i)$ with $\mathrm{Init}(p_0)$) satisfies: $\mathrm{Bad}(s)$ fails. Unpacking the witness $(p_i), i$ gives this form from the one above, and taking $s = p_i$ gives the one above back.

Hypotheses and conclusion quantify only over infinite paths; a state reachable from an initial state that lies on no infinite path, such as a state with no successor, is not covered.

## Sources

- M. Sheeran, S. Singh and G. Stålmarck, *Checking safety properties using induction and a SAT-solver*, Formal Methods in Computer-Aided Design (FMCAD 2000), LNCS 1954, Springer, 2000, pp. 127–144.
