# Black-box constructions and oracle separations

A *fully black-box construction* of a primitive $Q$ from a primitive $P$ consists of an oracle algorithm $G$ and an oracle reduction $S$ such that for every implementation $f$ of $P$, $G^f$ implements $Q$, and for every adversary $A$ breaking $G^f$ as an implementation of $Q$, $S^{f, A}$ breaks $f$ as an implementation of $P$. If there is an oracle relative to which $P$ exists but $Q$ does not, then no relativizing proof, and in particular no fully black-box construction, builds $Q$ from $P$.

## Depends on

- [Adaptive oracle algorithms](../../security-games/oracle-algorithms/oracle-comp.md)
- [Efficient adversaries](../../security-games/asymptotic-security/efficient-adversaries.md)

## Sources

- R. Impagliazzo and S. Rudich, "Limits on the provable consequences of one-way permutations", *Proceedings of the 21st ACM STOC*, 1989
- O. Reingold, L. Trevisan and S. Vadhan, "Notions of reducibility between cryptographic primitives", *TCC 2004*, LNCS 2951, Springer, 2004, Section 2 (fully black-box and relativizing reductions, Definition 6 and Proposition 1, item 7)
