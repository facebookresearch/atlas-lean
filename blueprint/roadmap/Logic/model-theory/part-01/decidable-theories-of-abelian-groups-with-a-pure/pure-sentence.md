# Prenex sentences about abelian groups and pure subgroups

A two-sorted prenex sentence of the language of an abelian group and its pure subgroups is coded as a pair $(q, \varphi)$. The prefix $q$ is a finite list of pairs (quantifier, sort): the quantifier is $\forall$ or $\exists$, and the sort is the element sort or the subgroup sort; the $j$-th quantifier binds the element variable $x_j$ or the subgroup variable $X_j$, according to its sort. The matrix $\varphi$ is in conjunctive normal form: a finite list of clauses (read as a conjunction), each a finite list of literals (read as a disjunction). A literal is an atom ($t = 0$, $t \in X_j$ or $X_i \subseteq X_j$, with $t$ a linear term) or its negation.

Every atomic formula of the two-sorted signature reduces effectively to these atoms ($t = s$ as $t - s = 0$, and $X = Y$ as two inclusions).
