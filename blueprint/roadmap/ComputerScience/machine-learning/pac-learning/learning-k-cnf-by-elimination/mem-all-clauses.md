# Initial clauses of the k-CNF elimination algorithm

Let $t, k \in \mathbb{N}$. Literals over $t$ Boolean variables are pairs $(i, b)$ with $i \in \{0, \dots, t-1\}$ and $b \in \{\text{true},\text{false}\}$ (the variable $p_i$ or its negation), and a clause is a finite set of literals. A clause $c$ belongs to the initial hypothesis of the elimination algorithm, the set of all clauses of at most $k$ literals over $t$ variables, if and only if

$$|c| \le k .$$

## Sources

L. G. Valiant, *A theory of the learnable*, Communications of the ACM 27 (1984), 1134–1142, Section 5, proof of Theorem A.
