# Query answering under weakly guarded tuple-generating dependencies is decidable

Given a database $D$, a [weakly guarded](guarded-and-weakly-guarded-tgds.md) set $\Sigma$ of TGDs and a Boolean conjunctive query
$Q$, it is decidable whether $D \cup \Sigma \models Q$. The proof bounds the treewidth of the whole chase by $|\mathrm{dom}(D)| + w$, where $w$ is the maximum
arity (Lemma 3.13 of the cited paper), and applies Courcelle's decidability of satisfiability for theories with the finite-treewidth model property.

## Depends on

- [Guarded and weakly guarded tuple-generating dependencies](guarded-and-weakly-guarded-tgds.md)

## Sources

- A. Calì, G. Gottlob and M. Kifer, "Taming the infinite chase: query answering under expressive relational constraints", *J. Artificial Intelligence Research* 48 (2013) 115–174; arXiv:1212.3357 <https://arxiv.org/abs/1212.3357>, Theorem 3.14 and its proof sketch.
