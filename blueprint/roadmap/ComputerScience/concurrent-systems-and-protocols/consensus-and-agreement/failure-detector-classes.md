# Failure detector classes

The eight failure detector classes pair two completeness conditions with four accuracy
conditions. The classes $\mathcal{P}$ (perfect), $\mathcal{S}$ (strong), $\Diamond\mathcal{P}$
(eventually perfect), and $\Diamond\mathcal{S}$ (eventually strong) use strong completeness and,
respectively, strong, weak, eventual strong, and eventual weak accuracy. The classes
$\mathcal{Q}$, $\mathcal{W}$, $\Diamond\mathcal{Q}$, and $\Diamond\mathcal{W}$ use weak completeness
with the same four accuracy conditions, in the same order.

## Model

The population of processes is finite. The natural-number ticks of the global clock index the
model; the clock is not available to the processes. A failure pattern $F$ gives the set $F(t)$
of processes that have crashed by tick $t$, including those crashing at that tick. These sets
are monotone in $t$. A process is *correct* if it never crashes, and there is at least one
correct process. It is *alive at tick $t$* if it is not in $F(t)$, even if it crashes later.

A history $H(q,t)$ gives the set of processes suspected by observer $q$ at tick $t$. A detector
$\mathcal{D}$ assigns a set $\mathcal{D}(F)$ of permitted histories to each pattern $F$.
The model does not require these sets to be nonempty and does not claim that a detector is
implementable. Reliable communication is the context of the classification, not part of this
specification of crash sets and histories.

## Completeness and accuracy

For every pattern $F$ and every history $H\in\mathcal{D}(F)$:

- *Strong completeness:* from some common tick onward, every correct observer suspects every
  process that crashes.
- *Weak completeness:* from some common tick onward, each process that crashes is permanently
  suspected by a fixed correct observer. The observer can differ between crashed processes,
  but cannot change with the tick.
- *Strong accuracy:* at each tick, no observer still alive suspects a target still alive.
- *Weak accuracy:* there is a fixed correct target that no observer suspects at any tick at
  which that observer is still alive, even if the observer crashes later.
- *Eventual strong accuracy:* from some tick onward, no correct observer suspects any correct
  target.
- *Eventual weak accuracy:* there is a tick and a fixed correct target that no correct observer
  suspects from that tick onward.

The eventual bounds include the cutoff tick. Because the process set is finite, there is a tick
after which the set of alive processes equals the fixed set of correct processes.

## Sources

- T. D. Chandra and S. Toueg, "Unreliable failure detectors for reliable distributed systems", *Journal of the ACM* 43(2):225–267, 1996, Sections 2.1–2.4 and Figure 1
