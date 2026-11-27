# Periodic tasks are feasible on a uniform platform matching their utilizations

Let $\tau = \{\tau_1, \dots, \tau_n\}$ be a periodic task system, in the sense of [global EDF scheduling](global-earliest-deadline-first-on-identical-multiprocessors.md), with utilizations $u_i = C_i/T_i \le 1$, at least one of them positive. There is a [uniform multiprocessor platform](uniform-multiprocessor-platforms.md) $\pi$ on which $\tau$ is feasible, whose fastest processor has speed $s_\pi = \max_i u_i$ and whose cumulative capacity is $S_\pi = U(\tau) = \sum_i u_i$. One such platform has one processor of speed $u_i$ for each task with $u_i > 0$: running every job of $\tau_i$ on its own processor from its arrival completes it in exactly $T_i$ time units, at its deadline.

## Depends on

- [Uniform multiprocessor platforms](uniform-multiprocessor-platforms.md)
- [Global earliest-deadline-first scheduling on identical multiprocessors](global-earliest-deadline-first-on-identical-multiprocessors.md)

## Sources

- J. Goossens, S. Funk and S. Baruah, *Priority-driven scheduling of periodic task systems on multiprocessors*, technical report TR01-024, Department of Computer Science, University of North Carolina at Chapel Hill, <http://www.cs.unc.edu/techreports/01-024.pdf>; published in *Real-Time Systems* 25(2–3):187–205, 2003; the section, theorem and footnote numbers below are those of the technical report, Section 2.2, Theorem 2, quoted there from S. Funk, J. Goossens and S. Baruah, "On-line scheduling on uniform multiprocessors", *Proceedings of the 22nd IEEE Real-Time Systems Symposium*, 2001. The platform with one processor per task is the construction behind the statement.
