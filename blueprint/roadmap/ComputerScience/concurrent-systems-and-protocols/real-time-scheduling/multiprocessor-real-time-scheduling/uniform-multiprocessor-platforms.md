# Uniform multiprocessor platforms

A *job* $J_j = (r_j, e_j, d_j)$ has an arrival time $r_j$, an execution requirement $e_j \ge 0$ and a deadline $d_j$: it needs $e_j$ units of execution within $[r_j, d_j)$. A *uniform multiprocessor platform* $\pi$ is a finite nonempty set of processors, each with a speed $\mathrm{speed}(P) > 0$: a job executing on $P$ for $t$ time units completes $\mathrm{speed}(P) \cdot t$ units of execution. Write $s_\pi = \max_{P \in \pi} \mathrm{speed}(P)$ for the speed of the fastest processor and $S_\pi = \sum_{P \in \pi} \mathrm{speed}(P)$ for the cumulative capacity; identical multiprocessors are the case where all speeds are $1$. A schedule of a set $I$ of jobs on $\pi$ assigns at each time at most one job to each processor and each job to at most one processor, with preemption and migration allowed; $I$ is *feasible* on $\pi$ if some schedule completes every job by its deadline. For an algorithm $A$, $W(A, \pi, I, t)$ is the amount of work $A$ does on the jobs of $I$ over $[0, t)$ on $\pi$. An algorithm on identical processors is *work-conserving* if it never leaves a processor idle while an active job is not executing; [global EDF](global-earliest-deadline-first-on-identical-multiprocessors.md) is work-conserving.

## Depends on

- [Global earliest-deadline-first scheduling on identical multiprocessors](global-earliest-deadline-first-on-identical-multiprocessors.md)

## Sources

- J. Goossens, S. Funk and S. Baruah, *Priority-driven scheduling of periodic task systems on multiprocessors*, technical report TR01-024, Department of Computer Science, University of North Carolina at Chapel Hill, <http://www.cs.unc.edu/techreports/01-024.pdf>; published in *Real-Time Systems* 25(2–3):187–205, 2003; the section, theorem and footnote numbers below are those of the technical report, Section 2.1 (jobs), Section 2.2, Definition 3 (uniform multiprocessors and the notation $s_\pi$, $S_\pi$), and Section 3, Definitions 4 and 5 (work-conserving algorithms, the work function $W$).
