# Complexity of query answering under guarded tuple-generating dependencies

Let $\Sigma$ be a set of [guarded TGDs](guarded-and-weakly-guarded-tgds.md) over a schema $\mathcal R$ with maximum predicate arity
$w$, let $D$ be a database and $Q$ a Boolean conjunctive query. Deciding $D \cup \Sigma \models Q$

1. is NP-complete when $w$ and $|\mathcal R|$ are bounded, even for a fixed set $\Sigma$;
2. is EXPTIME-complete when $w$ is bounded, and 2EXPTIME-complete in general, remaining 2EXPTIME-complete when $|\mathcal R|$ is bounded; and
3. for an atomic or fixed query $Q$, is PTIME-complete when $w$ and $|\mathcal R|$ are bounded, and remains PTIME-complete for a
   fixed set $\Sigma$, so the data complexity is polynomial.

## Depends on

- [Guarded and weakly guarded tuple-generating dependencies](guarded-and-weakly-guarded-tgds.md)
- [The complexity class NP](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/np.md)
- [The class EXP](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/exp.md)
- [The complexity class P](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)
- [NP-complete decision problems](../../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

- [Query answering under weakly guarded tuple-generating dependencies is decidable](query-answering-under-weakly-guarded-tgds-is-decidable.md)
- [GRAPH HOMOMORPHISM is NP-complete](../../../../TheoryOfComputation/np-completeness/graph-coloring-and-partitioning/graph-homomorphism/graph-homomorphism-np-complete.md)

## Sources

- A. Calì, G. Gottlob and M. Kifer, "Taming the infinite chase: query answering under expressive relational constraints", *J. Artificial Intelligence Research* 48 (2013) 115–174; arXiv:1212.3357 <https://arxiv.org/abs/1212.3357>, Theorem 6.1, items (2), (4) and (5).
