# Locally minimal rewritings reuse the query's atoms, and their view atoms can use the query's variables

Let $Q = q(\bar X) \mathrel{:-} p_1(\bar U_1), \dots, p_n(\bar U_n)$ be a conjunctive query and $\mathcal V$ a set of
conjunctive views, neither with built-in comparison atoms. Then:

1. in every locally minimal rewriting of $Q$ using $\mathcal V$, the set of database-relation atoms is isomorphic to
   a subset of the atoms of $Q$;
2. if $q(\bar X) \mathrel{:-} p_1(\bar U_1), \dots, p_n(\bar U_n), v_1(\bar Y_1), \dots, v_k(\bar Y_k)$ is a
   rewriting of $Q$ using $\mathcal V$, then so is some
   $q(\bar X) \mathrel{:-} p_1(\bar U_1), \dots, p_n(\bar U_n), v_1(\bar Y'_1), \dots, v_k(\bar Y'_k)$ whose view
   atoms use only variables of $\bar U_1, \dots, \bar U_n$. This is a choice, not a property of every rewriting: for
   $Q(x) \mathrel{:-} R(x, y)$ and the view $V(x, y, z) \mathrel{:-} R(x, y), R(x, z)$, the locally minimal rewriting
   $Q'(x) \mathrel{:-} V(x, y, z)$ uses the new variable $z$, while $Q''(x) \mathrel{:-} V(x, y, y)$ does not.

## Depends on

- [Rewritings of conjunctive queries using views](rewritings-of-conjunctive-queries-using-views.md)

## Proof depends on

- [Chandra-Merlin containment criterion](../conjunctive-queries/conjunctive-queries-and-the-chandra-merlin-theor/contained-iff-hom.md)

## Sources

- A. Y. Levy, A. O. Mendelzon, Y. Sagiv and D. Srivastava, "Answering queries using views", *Proceedings of the 14th ACM Symposium on Principles of Database Systems (PODS)*, 1995, pp. 95–104, Lemma 3.3 (p. 98).
