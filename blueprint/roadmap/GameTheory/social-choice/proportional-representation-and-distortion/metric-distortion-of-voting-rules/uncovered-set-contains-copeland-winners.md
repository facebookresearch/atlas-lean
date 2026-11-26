# The uncovered set is nonempty and contains every Copeland winner

Let $T$ be a tournament on a finite set $C$ of candidates, where $a \to b$ means that a strict majority prefers $a$ to $b$ (assume an odd number of voters with strict preferences). Candidate $a$ covers $b$ if $a \to b$ and $a \to c$ whenever $b \to c$. The uncovered set is the set of candidates covered by no other candidate. It is nonempty, every candidate maximizing the number of pairwise victories (a Copeland winner) is uncovered, and every uncovered candidate $a$ reaches every other candidate by a directed path of length at most $2$.

## Proof sketch

If $a$ covers $b$ then $a$ beats strictly more candidates than $b$ (all those beaten by $b$, plus $b$ itself), so a Copeland winner cannot be covered, which gives non-emptiness. If $a$ is uncovered and $b \to a$, then $b$ does not cover $a$, so some $c$ with $a \to c$ satisfies $c \to b$, a path of length two from $a$ to $b$.

## Depends on

- [Copeland score](../../../not-yet-classified/part-02/voting-rules/copeland-score.md)

## Sources

- N. R. Miller, "A New Solution Set for Tournaments and Majority Voting", American Journal of Political Science 24(1) (1980).
- F. Brandt, V. Conitzer, U. Endriss, J. Lang, A. D. Procaccia (eds.), "Handbook of Computational Social Choice", Cambridge University Press (2016).
