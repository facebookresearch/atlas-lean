# Guarded and weakly guarded tuple-generating dependencies

A tuple-generating dependency (TGD) $\sigma$ is a formula $\forall \bar X \forall \bar Y\, \Phi(\bar X, \bar Y) \to \exists \bar Z\, \Psi(\bar X, \bar Z)$
with conjunctions of atoms $\Phi$ (the body) and $\Psi$ (the head). Given a database $D$ and a set $\Sigma$ of TGDs, a Boolean
conjunctive query $Q$ is entailed, $D \cup \Sigma \models Q$, when $Q$ holds in every finite or infinite instance that contains $D$
and satisfies $\Sigma$; equivalently, when $Q$ holds in the result of a fair restricted chase of $D$ by $\Sigma$: a terminating chase sequence, or the
union of an infinite one in which every applicable trigger is eventually applied.

- $\sigma$ is *guarded* if some body atom, a guard, contains all universally quantified variables of $\sigma$.
- The set of positions *affected* with respect to $\Sigma$ is the least set containing every position $p[i]$ at which some
  $\sigma \in \Sigma$ has an existentially quantified variable in its head, and every position $p[i]$ at which the head of some
  $\sigma \in \Sigma$ has a variable that occurs in its body only at affected positions.
- $\sigma \in \Sigma$ is *weakly guarded* with respect to $\Sigma$ if some body atom contains every universally quantified variable
  of $\sigma$ that occurs in its body only at affected positions; $\Sigma$ is weakly guarded if all its TGDs are.

Every guarded set is weakly guarded. No labeled null of the chase occurs at a non-affected position.

## Depends on

- [Tuple- and equality-generating dependencies and the chase](../../dependencies-and-the-chase/tuple-and-equality-generating-dependencies-and-the-chase.md)
- [Answers of a conjunctive query](../../conjunctive-queries/answers-of-a-conjunctive-query.md)

## Sources

- A. Calì, G. Gottlob and M. Kifer, "Taming the infinite chase: query answering under expressive relational constraints", *J. Artificial Intelligence Research* 48 (2013) 115–174; arXiv:1212.3357 <https://arxiv.org/abs/1212.3357>, Definitions 2.1, 2.2, 3.1, 3.2 and 3.4, Example 3.3 and Theorem 2.10.
