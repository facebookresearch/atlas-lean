# Metric distortion of plurality, Borda and Copeland

In metric elections with $m$ candidates, plurality has distortion exactly $2m - 1$, the Borda count has distortion exactly $2m - 1$, and every rule that always selects a member of the uncovered set (in particular Copeland) has distortion at most $5$. Here $a$ weakly defeats $b$ if at least $n/2$ of the $n$ voters prefer $a$ to $b$, and a candidate $w$ is uncovered if for every other candidate $z$, either $w$ weakly defeats $z$ or $w$ weakly defeats some candidate $y$ that weakly defeats $z$; with pairwise ties both steps use weak defeat. The bound $5$ is tight for Copeland: for every $\varepsilon > 0$ there is a profile on three candidates on which its distortion is at least $5 - \varepsilon$. With two candidates Copeland only selects candidates preferred by at least half of the voters, whose distortion is at most $3$.

## Proof sketch

For an uncovered winner $w$, either $w$ weakly defeats the optimum $o$, which by a triangle-inequality argument over the at least $n/2$ voters preferring $w$ gives $\mathrm{SC}(w) \le 3\,\mathrm{SC}(o)$, or $w$ weakly defeats some $y$ that weakly defeats $o$, and a case analysis on whether $d(o, y) \ge d(o, w)$ gives $5$. Every Copeland winner is uncovered: a candidate weakly defeated by none of the winner and the candidates it beats would beat all of them and have a larger Copeland score. For plurality, voters for the winner might be located near it while most voters are near the optimum; the upper bound charges each voter's distance to the winner through her top choice. Matching lower-bound instances are explicit.

## Depends on

- [Metric election and distortion of a voting rule](metric-election-and-distortion.md)
- [Copeland score](../../../not-yet-classified/part-02/voting-rules/copeland-score.md)
- [Scoring Score](../../../not-yet-classified/part-02/voting-rules/scoring-score.md)

## Proof depends on

- [The uncovered set is nonempty and contains every Copeland winner](uncovered-set-contains-copeland-winners.md)

## Sources

- E. Anshelevich, O. Bhardwaj, E. Elkind, J. Postl, P. Skowron, "Approximating optimal social choice under metric preferences", Artificial Intelligence 264 (2018); AAAI 2015.
