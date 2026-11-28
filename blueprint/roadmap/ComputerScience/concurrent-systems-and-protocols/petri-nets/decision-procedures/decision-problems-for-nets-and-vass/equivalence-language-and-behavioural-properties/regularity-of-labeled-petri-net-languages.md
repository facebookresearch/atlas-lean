# Regularity of labeled Petri net languages is undecidable

It is undecidable whether the language of a labeled Petri net with respect to a final marking is a regular language, although regularity of the trace sets of unlabeled nets is decidable.

**Regularity problem.** For a labeled [Petri net](../../../place-transition-petri-nets.md) $(N, M_0)$ with labeling $\ell$ and a final marking $M^f$, the language is $L(N, M_0, M^f) = \{\ell(\sigma) : M_0 \xrightarrow{\sigma} M^f\}$. The regularity problem for languages of labeled nets asks, given $(N, M_0)$, $\ell$ and $M^f$, whether this language is regular.

**Theorem (Valk and Vidal-Naquet).** The regularity problem for languages of labeled Petri nets is undecidable.

By contrast, it is decidable whether the trace set (the set of all firing sequences from $M_0$) of an unlabeled Petri net is regular (Ginzburg and Yoeli; Valk and Vidal-Naquet), though not primitive recursive, and context-freeness of such trace sets is decidable (Schwer).

## Depends on

- [Place/transition Petri nets](../../../place-transition-petri-nets.md)
- [Language denoted by a regular expression](../../../../../../TheoryOfComputation/regular-languages/automata-and-expressions/kleene-s-theorem/is-regex-denoted.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The survey also cites Jantzen for the undecidability of regularity of labeled net languages, and gives no proof. The two problems differ in both the labeling and the use of a final marking, so the decidable case for unlabeled trace sets does not bear on the labeled language case.

## Sources

- Javier Esparza and Mogens Nielsen, "Decidability issues for Petri nets: a survey", *Journal of Information Processing and Cybernetics (EIK)* 30(3):143–160, 1994; read as arXiv:2411.01592v1, <https://arxiv.org/abs/2411.01592v1>: Section 2 (languages of labeled nets) and Section 3, paragraph "Regularity and context-freeness", of arXiv:2411.01592v1, which states the result.
- Rüdiger Valk and Guy Vidal-Naquet, "Petri nets and regular languages", *Journal of Computer and System Sciences* 23(3):299–325, 1981, doi:10.1016/0022-0000(81)90067-2 (not read; the original refereed source).
