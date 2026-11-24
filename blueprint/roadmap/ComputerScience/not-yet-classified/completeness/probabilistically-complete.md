# Probabilistically Complete

Probabilistically complete (LaValle, Planning Algorithms, Ch. 5 introduction;
MIT 16.410): sound, and on robustly feasible problems the probability of a found
answer by step N tends to 1.

The soundness clauses are the randomized analogues of `Planner.Sound`
(LaValle, Planning Algorithms, Ch. 4.3.1 Formulation 4.1 and Ch. 5 introduction).
The limit clause renders LaValle, Planning Algorithms, Ch. 5 introduction ("with
enough points, the probability that it finds an existing solution converges to one")
and MIT 16.410 (`lim Pr(ALG returns a solution) = 1` on robustly feasible
problems): the probability of having found by step `N` tends to `1`.
