# Truth of a prenex lattice sentence under an assignment

Let $L$ be a lattice, $\varphi$ a matrix (a finite list of clauses of literals $(b, i, j)$), $q$ a quantifier prefix (a finite list of booleans), $i \in \mathbb{N}$, and $x : \mathbb{N} \to L$ an assignment. Truth of the prenex formula with prefix $q$ and matrix $\varphi$, whose first quantifier binds $x_i$, is defined by recursion on $q$:

- for the empty prefix, the formula holds under $x$ if every clause $c$ of $\varphi$ contains a literal $(b, k, l)$ with $x_k \le x_l$ if and only if $b = \mathrm{true}$;
- for a prefix $\mathrm{true} :: q'$, it holds if for every $a \in L$ the formula with prefix $q'$, starting index $i + 1$, holds under the assignment $x[i \mapsto a]$;
- for a prefix $\mathrm{false} :: q'$, it holds if for some $a \in L$ the formula with prefix $q'$, starting index $i + 1$, holds under $x[i \mapsto a]$.

Here $x[i \mapsto a]$ agrees with $x$ except that it sends $i$ to $a$.
