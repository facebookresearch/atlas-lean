# Preemptive schedules of jobs on one processor

A *job* $J_j = (r_j, e_j, d_j)$ has a release time $r_j \ge 0$, an execution requirement $e_j \ge 0$ and an absolute deadline $d_j \ge r_j$, with the interpretation that it needs $e_j$ units of processor time within the interval $[r_j, d_j)$. Jobs are *independent*: they share no resource other than the processor and have no precedence constraints.

A *preemptive schedule* of finitely many jobs $J_1, \dots, J_n$ on one processor is a measurable map $\sigma : [0, \infty) \to \{0, 1, \dots, n\}$, where $\sigma(t) = j \ge 1$ means that $J_j$ executes at time $t$ and $\sigma(t) = 0$ that the processor is idle, such that no job executes before its release: $\sigma(t) = j$ implies $t \ge r_j$. A job may be interrupted and resumed later at no cost. Job $J_j$ *completes* at the least time $C_j \ge r_j$ at which the Lebesgue measure of $\{t < C_j : \sigma(t) = j\}$ equals $e_j$; if there is no such time it never completes. At time $t$ a job is *active* if $r_j \le t$ and it has not completed by $t$. A schedule is *feasible* if every job completes by its deadline, $C_j \le d_j$, and a set of jobs is *feasible* if it has a feasible schedule.

## Sources

- J. Goossens, S. Funk and S. Baruah, *Priority-driven scheduling of periodic task systems on multiprocessors*, technical report TR01-024, Department of Computer Science, University of North Carolina at Chapel Hill, <http://www.cs.unc.edu/techreports/01-024.pdf>; published in *Real-Time Systems* 25(2–3):187–205, 2003; the section, theorem and footnote numbers below are those of the technical report, Section 2.1: jobs $J_j = (r_j, e_j, d_j)$ that need $e_j$ units of execution over $[r_j, d_j)$.
- M. Sojka, *Deadline-driven scheduling*, lecture slides for Real-Time Systems, Czech Technical University in Prague, 22 November 2023, <https://rtime.felk.cvut.cz/psr/prednasky/3/03-rts.pdf>, slide 7: independent jobs with arbitrary release times and deadlines, preemption allowed.
