# Completion steps preserve the equational theory

If $E, R \vdash E', R'$ is a step of [Knuth–Bendix completion](knuth-bendix-completion.md) or of [unfailing completion](unfailing-completion.md), then the [equational theories](../../equational-logic/equational-consequence-and-e-algebras.md) of $E \cup R$ and $E' \cup R'$ coincide: $\approx_{E \cup R}\ =\ \approx_{E' \cup R'}$, rules $l \to r$ being read as equations $l \approx r$.

**Proof.** Each rule only adds or removes an equation or rule that is a consequence of the others: an oriented or simplified equation is obtained from the old one by rewriting steps with $R$, and a step of Deduce adds $s \approx t$ for a critical or semi-critical pair $\langle s, t \rangle$, which arises from an overlap $s \leftarrow u \to t$ of two members of $E \cup R$ and so is a consequence of them. Since $\approx_{E \cup R}$ is closed under replacement of equals, the two theories coincide.

## Depends on

- [Knuth–Bendix completion](knuth-bendix-completion.md)
- [Unfailing completion](unfailing-completion.md)
- [Equational consequence and E-algebras](../../equational-logic/equational-consequence-and-e-algebras.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.6, Lemma 4.33, p. 124, the remark on p. 122 that each step preserves the equational theory, and the note on p. 123 that a critical pair is a consequence of $R$; Section 4.7, the Deduce rule for semi-critical pairs, p. 128.
