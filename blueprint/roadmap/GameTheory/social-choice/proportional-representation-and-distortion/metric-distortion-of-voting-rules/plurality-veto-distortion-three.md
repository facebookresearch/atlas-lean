# Plurality Veto attains metric distortion three

The Plurality Veto rule works as follows. Each candidate $c$ starts with score $s(c) = \lvert \{ v : \mathrm{top}(v) = c \}\rvert$. Voters are processed in an arbitrary order $v_1, \dots, v_n$; voter $v_t$ decrements by one the score of her least preferred candidate among those with positive score. The last candidate whose score is decremented to zero is the winner. For every processing order, Plurality Veto has metric distortion at most $3$.

## Proof sketch

Pair each voter $v_t$ with a voter whose plurality point she removes: when $v_t$ vetoes candidate $c$, she consumes one unit of score contributed by some voter $v'$ with $\mathrm{top}(v') = c$, and since the winner $w$ still has positive score at that time, $v_t$ ranks $w$ above (or equal to) $c$. These pairings form a perfect matching of the domination graph $G_\sigma(w)$, and the matching certificate lemma gives distortion $3$.

## Depends on

- [Domination graph of a candidate](domination-graph-of-a-candidate.md)
- [Metric election and distortion of a voting rule](metric-election-and-distortion.md)

## Proof depends on

- [A perfect matching in the domination graph certifies distortion three](domination-matching-certifies-distortion-three.md)

## Sources

- F. E. Kizilkaya, D. Kempe, "Plurality Veto: A Simple Voting Rule Achieving Optimal Metric Distortion", IJCAI 2022, arXiv:2206.07098.
