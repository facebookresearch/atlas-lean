# Yannakakis' algorithm for acyclic join queries

Let $\mathbf{R}$ be an acyclic database schema with a join tree, and $I$ an instance over $\mathbf{R}$.
A bottom-up pass of semijoins along the join tree followed by a top-down pass is a full reducer: afterwards every
remaining tuple of every relation participates in the full join $\bowtie I$. Consequently, for every set of
attributes $X$, the expression $\pi_X(\bowtie I)$ can be computed in time polynomial in the size of $\mathbf{R}$, the
input instance and the output. For a Boolean acyclic conjunctive query $q$, a bottom-up semijoin pass decides
whether $q$ holds on a database $D$ in time $O(\|D\| \log \|D\| \cdot \|q\|)$.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: Conjunctive queries, answers and canonical databases.

## Proof depends on

- [Characterizations of acyclic database schemas](characterizations-of-acyclic-database-schemas.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995 (authors' web edition), Theorem 6.4.5 and its proof (full reducers) and Corollary 6.4.6. <http://webdam.inria.fr/Alice/pdfs/all.pdf>
- Database Theory, Lecture 14: efficient evaluation of acyclic conjunctive queries, University of Tartu, 2024, Algorithm 1 (Boolean acyclic queries) and the stated running time. <https://courses.cs.ut.ee/2024/datatheory/fall/Main/Lectures?action=download&upname=lec14.pdf>
