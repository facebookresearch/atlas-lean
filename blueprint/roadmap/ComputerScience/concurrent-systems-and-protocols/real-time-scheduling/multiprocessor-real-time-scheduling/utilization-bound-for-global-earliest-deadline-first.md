# Utilization bound for global earliest-deadline-first scheduling

A periodic task system $\tau$, in the sense of [global earliest-deadline-first scheduling on identical multiprocessors](global-earliest-deadline-first-on-identical-multiprocessors.md), with cumulative utilization $U(\tau)$ and largest task utilization $u_1 = \max_i u_i$, is EDF-schedulable on $m$ identical unit-speed processors if

$$
U(\tau) \le m - (m - 1)\,u_1 .
$$

Equivalently, $m \ge \lceil (U(\tau) - u_1)/(1 - u_1) \rceil$ processors suffice when $u_1 < 1$. For $u_1$ close to $1$ the bound approaches $1$ whatever $m$, the effect first observed by Dhall and Liu; with small task utilizations it approaches $m$.

## Depends on

- [Global earliest-deadline-first scheduling on identical multiprocessors](global-earliest-deadline-first-on-identical-multiprocessors.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- uniform multiprocessor platforms, on which processors may have different speeds (statement prerequisite of the proof);
- Theorem 2 of the source: a periodic task system is feasible on a uniform platform of cumulative capacity $U(\tau)$ whose fastest processor has speed $u_1$ (proof step);
- Lemma 1 and Theorem 3 of the source: if a set of jobs is feasible on one uniform platform, a work-conserving algorithm such as EDF meets all deadlines on any platform whose capacities satisfy the resource-augmentation condition there (proof step).

## Sources

- J. Goossens, S. Funk and S. Baruah, *Priority-driven scheduling of periodic task systems on multiprocessors*, technical report TR01-024, Department of Computer Science, University of North Carolina at Chapel Hill, <http://www.cs.unc.edu/techreports/01-024.pdf>; published in *Real-Time Systems* 25(2–3):187–205, 2003; the section, theorem and footnote numbers below are those of the technical report, Section 4, Theorems 4 and 5 (Theorem 5 is the bound above, Theorem 4 the processor count).
- R. I. Davis and A. Burns, "A survey of hard real-time scheduling for multiprocessor systems", *ACM Computing Surveys* 43(4), article 35, 2011; author version <https://www-users.york.ac.uk/~rd17/papers/MPSurveyv4.9.pdf>, Section 6 (the Dhall effect and utilisation bounds depending on the maximum task utilisation) and Section 6.1.1, equation (27) (the bound, attributed to Goossens et al. 2003).
