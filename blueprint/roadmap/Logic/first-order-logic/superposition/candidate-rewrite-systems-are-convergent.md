# Candidate rewrite systems are convergent

For the [candidate interpretation](candidate-interpretation-for-superposition.md) of a set of clauses, the rewrite systems $R_C$, for every $C \in G_\Sigma(N)$, and $R_\infty$ are convergent: terminating and confluent.

**Proof.** Every rule $s \to t$ has $s \succ t$, so the systems terminate. If $u \to v \in E_D$ and $s \to t \in E_C$ with $u$ a subterm of $s$ and $D \ne C$, then $u \preceq s$, so $D \prec_C C$, which puts $u \to v$ in $R_C$ and contradicts the irreducibility of $s$ with respect to $R_C$. Hence there are no critical pairs, the systems are locally confluent, and by Newman's lemma confluent.

## Depends on

- [Candidate interpretation for superposition](candidate-interpretation-for-superposition.md)
- [Confluence of a relation](../term-rewriting/confluence-of-a-relation.md)

## Proof depends on

- [Critical pair lemma](../automated-deduction/critical-pair-lemma.md)
- [Newman's lemma](../term-rewriting/newman-s-lemma.md)
- [Reduction orderings characterize termination](../term-rewriting/reduction-orderings-characterize-termination.md)

## Sources

- U. Waldmann, *Automated Reasoning II*, lecture notes, Max Planck Institute for Informatics, summer semester 2024, <https://rg1-teaching.mpi-inf.mpg.de/autrea2-ss24/notes-current.pdf>, Section 3.4, Lemma 3.2 and Corollary 3.3 with their proofs, pp. 54–55.
