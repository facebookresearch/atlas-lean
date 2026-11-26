# Tightness of the global earliest-deadline-first utilization bound

Let $m > 1$ be an integer, $0 < u_1 < 1$ and $0 < \varepsilon \le u_1$. There is a periodic task system, in the sense of [global earliest-deadline-first scheduling on identical multiprocessors](global-earliest-deadline-first-on-identical-multiprocessors.md), whose largest task utilization is $u_1$ and whose cumulative utilization is $m - (m - 1)u_1 + \varepsilon$, and which global EDF does not schedule on $m$ unit-speed processors. In the construction all tasks have period $p$, except that the task of utilization $u_1$ may be given a period infinitesimally larger than $p$ so that EDF runs its first job last; the other tasks then occupy all $m$ processors for longer than $(1 - u_1)p$, and that job misses its deadline. So the [utilization bound](utilization-bound-for-global-earliest-deadline-first.md) $m - (m-1)u_1$ cannot be raised.

## Depends on

- [Global earliest-deadline-first scheduling on identical multiprocessors](global-earliest-deadline-first-on-identical-multiprocessors.md)
- [Utilization bound for global earliest-deadline-first scheduling](utilization-bound-for-global-earliest-deadline-first.md)

## Sources

- J. Goossens, S. Funk and S. Baruah, *Priority-driven scheduling of periodic task systems on multiprocessors*, technical report TR01-024, Department of Computer Science, University of North Carolina at Chapel Hill, <http://www.cs.unc.edu/techreports/01-024.pdf>; published in *Real-Time Systems* 25(2–3):187–205, 2003, Section 4, Theorem 6, its proof and footnote 3.
