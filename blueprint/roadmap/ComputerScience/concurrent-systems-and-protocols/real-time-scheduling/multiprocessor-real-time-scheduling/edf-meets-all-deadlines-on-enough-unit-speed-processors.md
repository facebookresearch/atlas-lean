# EDF meets all deadlines on enough unit-speed processors

Let $\pi$ be a [uniform multiprocessor platform](uniform-multiprocessor-platforms.md) with cumulative capacity $S_\pi$ and fastest speed $s_\pi < 1$, and let $I$ be a set of jobs feasible on $\pi$. If $m' \ge (S_\pi - s_\pi)/(1 - s_\pi)$, then [global EDF](global-earliest-deadline-first-on-identical-multiprocessors.md) on $m'$ identical unit-speed processors meets every deadline of $I$. The jobs need not be known in advance.

**Proof.** Order the jobs by EDF priority and induct on the set $I_k$ of the $k$ highest-priority jobs: adding $J_{k+1}$ does not change how EDF schedules $J_1, \dots, J_k$. A schedule meeting all deadlines of $I_{k+1}$ on $\pi$ completes all its work $\sum_{i \le k+1} e_i$ by the latest deadline $d_{k+1}$ in $I_{k+1}$, so by the [work comparison](work-conserving-schedulers-keep-pace-with-any-schedule-on-a-slower-platform.md) EDF has done that much work by $d_{k+1}$, and $J_{k+1}$ completes by its deadline.

## Depends on

- [Uniform multiprocessor platforms](uniform-multiprocessor-platforms.md)
- [Global earliest-deadline-first scheduling on identical multiprocessors](global-earliest-deadline-first-on-identical-multiprocessors.md)

## Proof depends on

- [Work-conserving schedulers keep pace with any schedule on a slower platform](work-conserving-schedulers-keep-pace-with-any-schedule-on-a-slower-platform.md)

## Sources

- J. Goossens, S. Funk and S. Baruah, *Priority-driven scheduling of periodic task systems on multiprocessors*, technical report TR01-024, Department of Computer Science, University of North Carolina at Chapel Hill, <http://www.cs.unc.edu/techreports/01-024.pdf>; published in *Real-Time Systems* 25(2–3):187–205, 2003; the section, theorem and footnote numbers below are those of the technical report, Section 3, Theorem 3 with its proof.
