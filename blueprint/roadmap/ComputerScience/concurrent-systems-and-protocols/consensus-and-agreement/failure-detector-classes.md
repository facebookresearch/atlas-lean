# Failure detector classes

Consider $n$ processes $\Pi$ in an asynchronous system with reliable channels, and a discrete global clock with ticks $\mathbb{N}$ that the processes cannot read. A *failure pattern* is a function $F$ from times to sets of processes, $F(t)$ being the set of processes that have crashed by time $t$, with $F(t) \subseteq F(t+1)$; processes in $\mathrm{crashed}(F) = \bigcup_t F(t)$ *crash* and the others are *correct*, and at least one process is correct. A *failure detector history* $H$ assigns to each process $p$ and time $t$ the set $H(p, t)$ of processes that $p$ suspects at time $t$, and a *failure detector* $\mathcal{D}$ assigns to each failure pattern $F$ a set $\mathcal{D}(F)$ of histories. For every $F$ and every $H \in \mathcal{D}(F)$:

- *strong completeness*: there is a time after which every process that crashes is suspected by every correct process at all times;
- *weak completeness*: there is a time after which every process that crashes is suspected by some correct process at all times;
- *strong accuracy*: no process is suspected before it crashes;
- *weak accuracy*: some correct process is never suspected by any process that has not crashed;
- *eventual strong accuracy*: there is a time after which no correct process is suspected by any correct process;
- *eventual weak accuracy*: there is a time after which some correct process is never suspected by any correct process.

The classes $\mathcal{P}$ (perfect), $\mathcal{S}$ (strong), $\Diamond\mathcal{P}$ (eventually perfect) and $\Diamond\mathcal{S}$ (eventually strong) consist of the failure detectors with strong completeness and, respectively, strong, weak, eventual strong and eventual weak accuracy; $\mathcal{Q}$, $\mathcal{W}$, $\Diamond\mathcal{Q}$ and $\Diamond\mathcal{W}$ are the corresponding classes with weak completeness.

## Sources

- T. D. Chandra and S. Toueg, "Unreliable failure detectors for reliable distributed systems", *Journal of the ACM* 43(2):225–267, 1996, Sections 2.1–2.4 and Figure 1
