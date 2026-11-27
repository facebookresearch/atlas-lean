# Utilization bound for global earliest-deadline-first scheduling

A periodic task system $\tau$, in the sense of [global earliest-deadline-first scheduling on identical multiprocessors](global-earliest-deadline-first-on-identical-multiprocessors.md), with cumulative utilization $U(\tau)$ and largest task utilization $u_1 = \max_i u_i$, is EDF-schedulable on $m$ identical unit-speed processors if

$$
U(\tau) \le m - (m - 1)\,u_1 .
$$

Equivalently, $m \ge \lceil (U(\tau) - u_1)/(1 - u_1) \rceil$ processors suffice when $u_1 < 1$. For $u_1$ close to $1$ the bound approaches $1$ whatever $m$, the effect first observed by Dhall and Liu; with small task utilizations it approaches $m$.

**Proof.** If $U(\tau) = 0$, every job needs no execution and meets its deadline. Otherwise, for $u_1 < 1$, $\tau$ is feasible on a uniform platform with $s_\pi = u_1$ and $S_\pi = U(\tau)$, and the bound says $m \ge (U(\tau) - u_1)/(1 - u_1)$, so EDF meets every deadline of the jobs of $\tau$ on $m$ unit-speed processors. For $u_1 = 1$ the bound reads $U(\tau) \le 1$, so $\tau$ has one task of utilization $1$ and the others of utilization $0$, which EDF schedules on one processor.

## Depends on

- [Global earliest-deadline-first scheduling on identical multiprocessors](global-earliest-deadline-first-on-identical-multiprocessors.md)

## Proof depends on

- [Periodic tasks are feasible on a uniform platform matching their utilizations](periodic-tasks-are-feasible-on-a-uniform-platform-matching-their-utilizations.md)
- [EDF meets all deadlines on enough unit-speed processors](edf-meets-all-deadlines-on-enough-unit-speed-processors.md)

## Sources

- J. Goossens, S. Funk and S. Baruah, *Priority-driven scheduling of periodic task systems on multiprocessors*, technical report TR01-024, Department of Computer Science, University of North Carolina at Chapel Hill, <http://www.cs.unc.edu/techreports/01-024.pdf>; published in *Real-Time Systems* 25(2–3):187–205, 2003; the section, theorem and footnote numbers below are those of the technical report, Section 4, Theorems 4 and 5 with their proofs (Theorem 5 is the bound above, Theorem 4 the processor count).
- R. I. Davis and A. Burns, "A survey of hard real-time scheduling for multiprocessor systems", *ACM Computing Surveys* 43(4), article 35, 2011; author version <https://www-users.york.ac.uk/~rd17/papers/MPSurveyv4.9.pdf>, Section 6 (the Dhall effect and utilisation bounds depending on the maximum task utilisation) and Section 6.1.1, equation (27) (the bound, attributed to Goossens et al. 2003).
