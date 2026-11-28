# MinWork is a truthful n-approximation for unrelated scheduling

For scheduling jobs on $n$ unrelated machines with private processing-time vectors, the MinWork mechanism, which assigns each job to a machine of minimum reported time and pays that machine the second-smallest reported time for the job, is a Groves (VCG) mechanism and hence DSIC, and its makespan is at most $n$ times the optimal makespan.

## Proof sketch

Minimizing total work maximizes the negated total cost, so second-price payments per job are Clarke pivots. Total minimum work is at most the total work of an optimal schedule, which is at most $n$ times the optimal makespan.

## Depends on

- [MinWork allocation](../../not-yet-classified/part-02/truthful-scheduling/min-work.md)
- [Is Truthful](../../not-yet-classified/part-02/truthful-scheduling/is-truthful.md)

## Proof depends on

- [Vickrey–Clarke–Groves theorem](../vickrey-clarke-groves-mechanisms/is-incentive-compatible-groves.md)

## Sources

- Noam Nisan and Amir Ronen, "Algorithmic Mechanism Design", Games and Economic Behavior, 2001.
- Ron Lavi, "Computationally Efficient Approximation Mechanisms", Algorithmic Game Theory, Cambridge University Press, 2007.
