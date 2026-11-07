# Lossless decomposition into two schemes

Let $F$ be a finite set of functional
dependencies, let $R_1$ and $R_2$ be finite sets of attributes, and let $D$ be a type of values.
The decomposition of $R_1 \cup R_2$ into $R_1$ and $R_2$ is lossless for $F$ with values in $D$
when every relation $r$ over $R_1 \cup R_2$ with values in $D$ that satisfies $F$ on
$R_1 \cup R_2$ (every dependency $X \to Y$ with $X, Y \subseteq R_1 \cup R_2$ that is derivable
from $F$ by Armstrong's axioms holds in $r$) is the natural join of its projections:
$\pi_{R_1}(r) \bowtie \pi_{R_2}(r) = r$.
