# Plurality and the Borda count versus Condorcet winners

A Condorcet winner, an alternative beating every other in pairwise majority, is unique when it exists, and with at least three voters and three alternatives there are profiles with no Condorcet winner. For at least three voters and three alternatives, the plurality rule (ties broken by a fixed order of the alternatives) is onto, non-dictatorial, not strategy-proof, and not Condorcet consistent (it can fail to select an existing Condorcet winner). For at least two voters and three alternatives, the Borda count is Pareto and non-dictatorial but violates independence of irrelevant alternatives.

## Proof sketch

Uniqueness: two Condorcet winners would each strictly beat the other. Explicit three-alternative profiles exhibit each failure; the Borda IIA violation moves a third alternative between two others.

## Depends on

- [Social choice functions](../gibbard-satterthwaite-theorem/social-choice-function.md)
- [Social welfare function](../arrow-s-impossibility-theorem/social-welfare-function.md)
- [Independence of irrelevant alternatives](../arrow-s-impossibility-theorem/is-iia.md)
- [Scoring Score](../voting-rules-and-majority-relations/voting-rules/scoring-score.md)

## Proof depends on

- [Condorcet paradox](../voting-rules-and-majority-relations/condorcet-paradox-a-majority-cycle/exists-is-majority-cycle.md)

## Sources

- Noam Nisan, "Introduction to Mechanism Design (for Computer Scientists)", Algorithmic Game Theory, Cambridge University Press, 2007.
