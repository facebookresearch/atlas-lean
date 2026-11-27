# Round robin is 2-competitive for total completion time

For non-clairvoyant scheduling of $n$ jobs on one machine, the round-robin (processor-sharing) schedule, which runs all unfinished jobs at equal rates, has total completion time at most $2\sum_j C_j^{\mathrm{SPT}}$, where $C^{\mathrm{SPT}}$ denotes completion times under shortest processing time first; no deterministic non-clairvoyant algorithm has a better ratio as $n \to \infty$.

## Proof sketch

Sort $p_1 \le \dots \le p_n$. Under processor sharing, job $j$ completes at $C_j = \sum_{i < j} p_i + (n - j + 1) p_j$, so $\sum_j C_j = \sum_j (2(n - j) + 1) p_j$, while $\sum_j C^{\mathrm{SPT}}_j = \sum_j (n - j + 1) p_j$; the ratio of coefficients is at most $2$. The matching lower bound, also due to Motwani, Phillips and Torng, shows that for every $\varepsilon > 0$ and all large $n$ some instance forces every deterministic non-clairvoyant algorithm above ratio $2 - \varepsilon$.

## Depends on

- [Non-clairvoyant scheduling with predicted job sizes](nonclairvoyant-scheduling-with-predictions.md)

## Sources

- Rajeev Motwani, Steven Phillips, Eric Torng, "Nonclairvoyant Scheduling", Theoretical Computer Science 130(1) (1994).
