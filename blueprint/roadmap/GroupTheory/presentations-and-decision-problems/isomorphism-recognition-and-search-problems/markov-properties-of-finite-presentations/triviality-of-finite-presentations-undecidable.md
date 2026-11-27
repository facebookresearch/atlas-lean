# Triviality of finitely presented groups is undecidable

No algorithm decides, given a finite presentation, whether it presents the trivial group; consequently the isomorphism problem for finite presentations is undecidable.

**Theorem (Adian; Rabin).** There is no algorithm that takes as input a finite presentation $\langle x_1, \dots, x_n \mid r_1, \dots, r_m \rangle$ and decides whether the group it presents is trivial.

Since triviality is the special case of isomorphism in which one presentation is fixed to be $\langle \ \mid \ \rangle$, there is also no algorithm deciding whether two finite presentations define isomorphic groups.

## Depends on

- [Group](../../../group-basics/group.md)

## Proof depends on

- [Adian–Rabin theorem: Markov properties of finitely presented groups are undecidable](adian-rabin-theorem.md)

## Expansion

Being trivial is a Markov property: the trivial group has it, and any nontrivial finitely presented group, for instance $\mathbb{Z}$, embeds in no trivial group, since the property is inherited by subgroups. The Adian–Rabin theorem then applies directly.

## Sources

- Bjorn Poonen, *Undecidable problems: a sampler*, in: Interpreting Gödel: Critical Essays (J. Kennedy, ed.), Cambridge University Press, 2014, pp. 211–241, https://doi.org/10.1017/CBO9780511756306.015, read in the copy arXiv:1204.0299v2, where the statement is Corollary 6.3 and the consequence for the isomorphism problem follows it.
- Michael O. Rabin, *Recursive unsolvability of group theoretic problems*, Ann. of Math. (2) 67 (1958), no. 1, 172–194, https://doi.org/10.2307/1969933, cited beside the survey read above.
