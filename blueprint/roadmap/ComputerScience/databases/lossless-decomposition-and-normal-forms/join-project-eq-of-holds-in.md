# Heath's theorem

Let $A$ be a finite set of attributes, $D$ a type of values, $R_1, R_2 \subseteq A$ schemes, and
let $r$ be a relation over $R_1 \cup R_2$, that is, a finite set of tuples each defined exactly on
the attributes of $R_1 \cup R_2$. If the functional dependency $R_1 \cap R_2 \to R_1$ holds in
$r$, then $r$ is the natural join of its projections onto $R_1$ and $R_2$:
$\pi_{R_1}(r) \bowtie \pi_{R_2}(r) = r$.
