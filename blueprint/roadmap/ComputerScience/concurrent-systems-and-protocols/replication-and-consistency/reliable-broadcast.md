# Reliable broadcast

Reliable broadcast is a communication primitive for asynchronous systems in which processes may crash. It is given by two primitives, $\mathrm{R\text{-}broadcast}(m)$ and $\mathrm{R\text{-}deliver}(m)$, where every message $m$ carries the identity $\mathrm{sender}(m)$ of its sender, a sequence number and a payload; in the source, the sender and the sequence number make every message unique. A run of a system of processes is recorded by the set of its *correct* processes and by its events: at each time $t = 0, 1, 2, \dots$ there is at most one event, in which a process R-broadcasts or R-delivers a message. The run satisfies *reliable broadcast* if it has the following properties:

- *validity*: if a correct process $p$ R-broadcasts $m$ at time $t$, then $p$ R-delivers $m$ at some time $t' \ge t$;
- *agreement*: if a correct process $p$ R-delivers $m$, then every correct process $q$ R-delivers $m$ at some time, possibly before $p$ does;
- *uniform integrity*: every process, correct or not, R-delivers each message $m$ at most once, and only at a time $t$ such that $\mathrm{sender}(m)$ R-broadcasts $m$ at some time $t' < t$.

## Sources

- T. D. Chandra and S. Toueg, "Unreliable failure detectors for reliable distributed systems", *Journal of the ACM* 43(2):225–267, 1996, Section 4
