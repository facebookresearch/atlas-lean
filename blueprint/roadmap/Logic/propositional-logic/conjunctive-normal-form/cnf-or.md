# Disjoining CNF builder

Let $\iota$ number the atoms by natural numbers, read a literal
$(n, p)$ as variable $n$ with polarity $p$, and write $1$ and $0$ for the polarities true and
false. For a polarity $p$, a proposition $\varphi$ and a CNF $S$, the CNF
$\mathcal{O}_p(\varphi, S)$ is defined by recursion on $\varphi$, together with the accumulating
CNF builder $\mathcal{A}_p$. Write $X \otimes S$ for the disjunction of two CNFs $X$ and $S$ and
$[\,]$ for the empty CNF. For an atom $a$, $\mathcal{O}_p(a, S) = U \otimes S$, where $U$ is the
CNF whose only clause is the unit clause $[(\iota(a), p)]$. Disjunction-like nodes are consumed
from the left: $\mathcal{O}_1(A \lor B, S) = \mathcal{O}_1(A, \mathcal{O}_1(B, S))$,
$\mathcal{O}_1(A \to B, S) = \mathcal{O}_0(A, \mathcal{O}_1(B, S))$ and
$\mathcal{O}_0(A \land B, S) = \mathcal{O}_0(A, \mathcal{O}_0(B, S))$. Conjunction-like nodes go
through $\mathcal{A}$:
$\mathcal{O}_1(A \land B, S) = \mathcal{A}_1(A, \mathcal{A}_1(B, [\,])) \otimes S$,
$\mathcal{O}_0(A \lor B, S) = \mathcal{A}_0(A, \mathcal{A}_0(B, [\,])) \otimes S$ and
$\mathcal{O}_0(A \to B, S) = \mathcal{A}_1(A, \mathcal{A}_0(B, [\,])) \otimes S$.

An assignment $\sigma$ satisfies $\mathcal{O}_p(\varphi, S)$ exactly when $\varphi$ has truth
value $p$ under $\sigma \circ \iota$ or $\sigma$ satisfies $S$.
