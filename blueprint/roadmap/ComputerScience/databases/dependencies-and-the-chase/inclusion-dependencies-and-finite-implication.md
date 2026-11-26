# Inclusion dependencies and finite implication

Let $R$ and $S$ be relation names in the same schema; they need not be different. An [inclusion dependency](ind.md) chooses an ordered sequence $A_1,\ldots,A_k$ of distinct attributes of $R$ and an ordered sequence $B_1,\ldots,B_k$ of distinct attributes of $S$. An instance $I$ satisfies $R[A_1,\ldots,A_k]\subseteq S[B_1,\ldots,B_k]$ exactly when

$$
\{(t(A_1),\ldots,t(A_k)):t\in I(R)\}
\;\subseteq\;
\{(s(B_1),\ldots,s(B_k)):s\in I(S)\}.
$$

For each source row $t$ there must be [one target row](holds-in-iff-exists-row.md) $s$ with $t(A_i)=s(B_i)$ for every position $i$. Matching one column at a time does not suffice: the row $(0,1)$ has each of its values matched in the corresponding column of $\{(0,0),(1,1)\}$, but neither target row matches the ordered pair.

A set of hypotheses may contain both [functional and inclusion dependencies](dependency.md). [Unrestricted implication](implies.md) asks whether every whole instance satisfying all the hypotheses also satisfies the conclusion. [Finite implication](finitely-implies.md) asks the same question only of instances with finite relation extents. Both use the same value domain; the natural numbers give the book's countably infinite domain up to renaming. Since there are finitely many relation names and each row has finitely many attributes, [finiteness of the extents is equivalent to finiteness of the active domain](is-finite-iff-finite-active-domain.md), the values that actually occur.

## Sources

- S. Abiteboul, R. Hull and V. Vianu, [*Foundations of Databases*](https://webdam.di.ens.fr/Alice/pdfs/all.pdf), Addison-Wesley, 1995. Definition 9.1.1 (p. 193) gives the syntax and satisfaction condition; Definition 9.2.1 (p. 198) distinguishes unrestricted and finite implication.
