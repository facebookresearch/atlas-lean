# Rewritings of conjunctive queries using views

Views $V_1, \dots, V_m$ are conjunctive queries over the database relation names, each with its own view name.
A rewriting of a conjunctive query $Q$ using views $\mathcal V = \{V_1, \dots, V_m\}$ is a conjunctive query $Q'$
over the database relation names and the view names that is equivalent to $Q$ (when each view atom is interpreted by
the view's answer, $Q'$ returns the same answer as $Q$ on every database) and contains at least one atom of a view. The expansion of $Q'$ replaces each view atom by the view's body with fresh existential
variables, so a query $Q'$ that contains at least one view atom is a rewriting exactly when its expansion is equivalent to $Q$. A rewriting is locally minimal if
no atom can be removed from it while keeping equivalence with $Q$, and globally minimal if no rewriting has fewer
atoms (built-in comparison atoms $=, \ne, <, \le$ are not counted); it is complete if it contains only view atoms and
built-in atoms. For example, $q(X, U) \mathrel{:-} v(X, Z), p_1(X, W), p_2(W, U)$ rewrites
$q(X, U) \mathrel{:-} p(X, Y), p'(Y, Z), p_1(X, W), p_2(W, U)$ using $v(A, B) \mathrel{:-} p(A, C), p'(C, B), p_1(A, D)$,
but the atom $p_1(X, W)$ cannot be dropped because $D$ is projected out of the view.

## Depends on

- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)

## Sources

- A. Y. Levy, A. O. Mendelzon, Y. Sagiv and D. Srivastava, "Answering queries using views", *Proceedings of the 14th ACM Symposium on Principles of Database Systems (PODS)*, 1995, pp. 95–104, Definition 2.1, Example 2.2, Definition 2.4 and the expansions used in Section 3 (pp. 96–99).
