# Plurality and the Borda count versus Condorcet winners

A Condorcet winner, an alternative beating every other in pairwise majority, is unique when it exists, and with at least three voters and three alternatives there are profiles with no Condorcet winner. For at least three voters and three alternatives, the plurality rule (ties broken by a fixed order of the alternatives) is onto, non-dictatorial and not strategy-proof, and, except for exactly four voters with exactly three alternatives, it is not Condorcet consistent (it can fail to select an existing Condorcet winner). For at least two voters and three alternatives, the Borda count is Pareto and non-dictatorial but violates independence of irrelevant alternatives.

## Proof sketch

Uniqueness: two Condorcet winners would each strictly beat the other. Explicit profiles exhibit each failure (for Condorcet consistency with four voters, one with four alternatives), and alternatives ranked last by every voter extend them to more alternatives; the Borda IIA violation moves a third alternative between two others. With four voters and three alternatives, a Condorcet winner beats each other alternative in at least three of the four rankings, so at least two voters rank it first while each other alternative is ranked first by at most one, and plurality selects it.

## Depends on

- [Social choice functions](../gibbard-satterthwaite-theorem/social-choice-function.md)
- [Social welfare function](../arrow-s-impossibility-theorem/social-welfare-function.md)
- [Independence of irrelevant alternatives](../arrow-s-impossibility-theorem/is-iia.md)
- [Scoring Score](../../not-yet-classified/part-02/voting-rules/scoring-score.md)

## Proof depends on

- [Condorcet paradox](../../not-yet-classified/part-01/condorcet-cycle/exists-is-majority-cycle.md)

## Sources

- Noam Nisan, "Introduction to Mechanism Design (for Computer Scientists)", Algorithmic Game Theory, Cambridge University Press, 2007.
