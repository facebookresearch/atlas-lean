# Rounding processing times to ticks

Let a finite list of jobs have real processing times $p_j \ge 0$, let $\delta > 0$, and let
$\tilde p_j = \lceil p_j/\delta \rceil\in\mathbb{N}$ be their tick counts. For a fixed assignment
$S = (S_1, \dots, S_m)$ of every job occurrence exactly once to $m \ge 1$ machines, define the real load maximum
$C(S)=\max_i\sum_{j\in S_i}p_j$. Let $\tilde C(S)$ be the natural-number makespan of the lists of tick counts assigned to
those same machines. Cast it to a real number before multiplying by $\delta$. Then

$$C(S) \le \delta\,\tilde C(S) \le C(S) + \delta \max_i \lvert S_i\rvert,$$

since $p_j \le \delta \tilde p_j < p_j + \delta$ for every job. The additive term can be much larger than $\delta$: one hundred
jobs of time $0.01$ on one machine with $\delta = 1$ give $C(S) = 1$ and $\delta\,\tilde C(S) = 100$. Setup and sequence-dependent
times are outside this result.

## Depends on

- [Makespan](makespan.md)

## Proof depends on

## Sources

- Derived on this page from the linked definition of the makespan: the bound follows from $p_j \le \delta \tilde p_j < p_j + \delta$ for each job, summed over each machine. No external source is followed.
