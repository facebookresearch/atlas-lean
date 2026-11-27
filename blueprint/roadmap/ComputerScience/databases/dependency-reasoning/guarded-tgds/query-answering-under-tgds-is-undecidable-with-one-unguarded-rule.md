# Query answering under tuple-generating dependencies is undecidable with a single unguarded rule

There are a fixed atomic Boolean conjunctive query $Q$ and a fixed set $\Sigma_u$ of TGDs, all
[guarded](guarded-and-weakly-guarded-tgds.md) except one, such that deciding $D \cup \Sigma_u \models Q$ for an input database $D$
is undecidable. The unguarded rule lets the chase build an infinite grid, on which guarded rules simulate a Turing machine.

## Depends on

- [Guarded and weakly guarded tuple-generating dependencies](guarded-and-weakly-guarded-tgds.md)

## Sources

- A. Calì, G. Gottlob and M. Kifer, "Taming the infinite chase: query answering under expressive relational constraints", *J. Artificial Intelligence Research* 48 (2013) 115–174; arXiv:1212.3357 <https://arxiv.org/abs/1212.3357>, Theorem 3.5 and its proof.
