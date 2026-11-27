# Global earliest-deadline-first scheduling on identical multiprocessors

A *periodic task* $\tau_i = (C_i, T_i)$, with execution requirement $C_i \ge 0$ and period $T_i > 0$, generates a job at each integer multiple $kT_i$ ($k = 0, 1, 2, \dots$) of its period; the job needs $C_i$ units of execution and must complete by the next multiple $(k+1)T_i$. Its utilization is $u_i = C_i/T_i \le 1$. For a periodic task system $\tau = \{\tau_1, \dots, \tau_n\}$ the cumulative utilization is $U(\tau) = \sum_i u_i$. Jobs are independent and preemptive; a preempted job may resume on any processor at no cost, but executes on at most one processor at a time.

On a platform of $m$ identical processors of unit speed, *global earliest-deadline-first* (EDF) scheduling executes at every time the active jobs with the earliest deadlines, as many of them as there are processors (all active jobs if there are at most $m$), with ties between equal deadlines broken arbitrarily. The task system is *EDF-schedulable* on the platform if every job meets its deadline.

## Depends on

- [Earliest-deadline-first schedules](../deadline-driven-scheduling/earliest-deadline-first-schedules.md)

## Sources

- J. Goossens, S. Funk and S. Baruah, *Priority-driven scheduling of periodic task systems on multiprocessors*, technical report TR01-024, Department of Computer Science, University of North Carolina at Chapel Hill, <http://www.cs.unc.edu/techreports/01-024.pdf>; published in *Real-Time Systems* 25(2–3):187–205, 2003; the section, theorem and footnote numbers below are those of the technical report, Section 1 (the periodic task model, jobs at each integer multiple of the period, preemption) and Section 2.
- R. I. Davis and A. Burns, "A survey of hard real-time scheduling for multiprocessor systems", *ACM Computing Surveys* 43(4), article 35, 2011; author version <https://www-users.york.ac.uk/~rd17/papers/MPSurveyv4.9.pdf>, Sections 2.3 and 6 (global scheduling with migration of jobs between processors).
