# Metric distortion of plurality, Borda and Copeland

In metric elections with $m$ candidates, plurality has distortion exactly $2m - 1$, the Borda count has distortion exactly $2m - 1$, and every rule that always selects a member of the uncovered set, the candidates $b$ for which no candidate beats $b$ in pairwise majority together with every candidate that $b$ beats (in particular Copeland), has distortion at most $5$; Copeland's distortion is exactly $5$.

## Proof sketch

For Copeland, a winner $w$ either beats the optimum $o$ in pairwise majority, which by a triangle-inequality argument over the majority preferring $w$ gives $\mathrm{SC}(w) \le 3\,\mathrm{SC}(o)$, or beats some $y$ that beats $o$, and composing the two-step bound gives $5$. For plurality, voters for the winner might be located near it while most voters are near the optimum; the upper bound charges each voter's distance to the winner through her top choice. Matching lower-bound instances are explicit.

## Depends on

- [Metric election and distortion of a voting rule](metric-election-and-distortion.md)
- [Copeland score](../../../not-yet-classified/part-02/voting-rules/copeland-score.md)
- [Scoring Score](../../../not-yet-classified/part-02/voting-rules/scoring-score.md)

## Proof depends on

- [The uncovered set is nonempty and contains every Copeland winner](uncovered-set-contains-copeland-winners.md)

## Sources

- E. Anshelevich, O. Bhardwaj, E. Elkind, J. Postl, P. Skowron, "Approximating optimal social choice under metric preferences", Artificial Intelligence 264 (2018); AAAI 2015.
