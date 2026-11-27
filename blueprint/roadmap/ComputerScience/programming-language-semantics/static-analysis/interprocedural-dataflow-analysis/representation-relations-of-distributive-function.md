# Representation relations of distributive functions

Let $D$ be a finite set and $0 \notin D$ a new element. For a function $f : 2^D \to 2^D$, its *representation relation* is

$$R_f = \{(0, 0)\} \cup \{(0, y) \mid y \in f(\emptyset)\} \cup \{(x, y) \mid y \in f(\{x\}),\ y \notin f(\emptyset)\} \subseteq (D \cup \{0\}) \times (D \cup \{0\}),$$

a bipartite graph with at most $(|D| + 1)^2$ edges. A relation $R$ on $D \cup \{0\}$ is *interpreted* as the function

$$[\![R]\!](X) = \bigl(\{y \mid \exists x \in X.\ (x, y) \in R\} \cup \{y \mid (0, y) \in R\}\bigr) \setminus \{0\}.$$

Write $R_f ; R_g$ for relational composition, and call $f$ *distributive* if $f(X \cup Y) = f(X) \cup f(Y)$ for all $X, Y \subseteq D$. A problem whose meet is intersection is first complemented. Preservation of intersections does not suffice: on $D = \{a, b\}$, the function with $f(D) = \{a\}$ and $f(X) = \emptyset$ for $X \ne D$ preserves binary intersections, but $[\![R_f]\!](D) = \emptyset$.

1. If $f$ is distributive, $[\![R_f]\!] = f$.
2. For all distributive $f, g : 2^D \to 2^D$, $[\![R_f ; R_g]\!] = g \circ f$.
3. Consequently, any composite $f_k \circ \dots \circ f_1$ of distributive functions is represented by paths in the graph obtained by chaining $R_{f_1}, \dots, R_{f_k}$: for $y \in D$, $y \in (f_k \circ \dots \circ f_1)(X)$ if and only if there is a path from a node of $X \cup \{0\}$ in the first layer to $y$ in the last.

Distributivity is what lets $f$ be recovered from its values on $\emptyset$ and on singletons: $f(X) = f(\emptyset) \cup \bigcup_{x \in X} f(\{x\})$.

## Sources

- T. Reps, S. Horwitz and M. Sagiv, "Precise interprocedural dataflow analysis via graph reachability", *Conference Record of the 22nd ACM Symposium on Principles of Programming Languages (POPL 1995)*, <https://research.cs.wisc.edu/wpis/papers/popl95.pdf>: Section 3.1, Definition 3.1 (representation relations), Definition 3.2 (interpretation), Theorem 3.3, Definition 3.4 and Theorem 3.5 (composition), and Corollary 3.6.
- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, version of October 15, 2026, <https://cs.au.dk/~amoeller/spa/>: Section 9.3 (compact representation of distributive functions).
