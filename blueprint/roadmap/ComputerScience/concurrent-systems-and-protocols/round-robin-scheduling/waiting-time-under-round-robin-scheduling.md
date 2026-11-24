# Waiting time under round-robin scheduling

Consider round-robin scheduling of a fixed set of $n$ jobs kept in a cyclic ready queue, with time quantum $q \ge 0$, zero context-switch cost, no new arrivals and no blocking: the job at the head of the queue runs for $q$ time units or until it finishes, and if unfinished it rejoins the tail of the queue. Then every job that has not finished waits at most $(n - 1)q$ time units between the end of one of its quanta and the start of its next.

## Expansion

This page becomes ready once these prerequisites are stated:

- Round-robin ready-queue operational model (statement prerequisite)

## Sources

- R. H. Arpaci-Dusseau and A. C. Arpaci-Dusseau, *Operating Systems: Three Easy Pieces*, Arpaci-Dusseau Books, 2018, Chapter 7, Section 7.7 "Round Robin", <https://pages.cs.wisc.edu/~remzi/OSTEP/cpu-sched.pdf>
