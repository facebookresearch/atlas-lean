# A polling driver simulates the sampled-register specification

A polling driver is the labelled transition system with local states $\mathsf{idle}$, $\mathsf{polled}$ and
$\mathsf{got}(n, v)$ and actions: $\mathsf{poll}$, a $\mathsf{Ready}$ access from $\mathsf{idle}$ that moves to $\mathsf{polled}$
if the slot is nonempty and stays in $\mathsf{idle}$ otherwise; $\mathsf{read}$, an atomic $\mathsf{Read}$ from $\mathsf{polled}$
that moves to $\mathsf{got}(n, v)$ on a pair and back to $\mathsf{idle}$ on $\bot$; $\mathsf{emit}(n, v)$, from $\mathsf{got}(n, v)$
back to $\mathsf{idle}$; and internal steps that change neither the register nor the driver's view of it. Its register accesses are
sequentially consistent: each is one atomic step of the [sampled register](overwrite-register-reads-return-increasing-publications.md). Compose the driver with the register and with an environment that performs $\mathsf{Publish}$ events at any
time. Then the map that erases the driver's local state is a simulation of the composition by the register: every step of the
composition is matched by one register step ($\mathsf{Publish}$, or the $\mathsf{Read}$ of a $\mathsf{read}$) or by none
($\mathsf{poll}$, $\mathsf{emit}$ and internal steps), so erasing the unmatched steps turns every run into a trace of the
register. Moreover each $\mathsf{emit}(n, v)$ is preceded by a successful $\mathsf{Read}$ returning $(n, v)$ that no earlier emit
used. Hence the emitted samples have strictly increasing publication numbers and carry the values of those publications.

## Depends on

- [Reads of an overwrite-newest register return increasing publications](overwrite-register-reads-return-increasing-publications.md)

## Sources

- H. Kopetz, *Real-Time Systems: Design Principles for Distributed Embedded Applications*, 2nd edition, Springer, 2011, Chapter 4 (state messages with update-in-place semantics).
- N. A. Lynch, *Distributed Algorithms*, Morgan Kaufmann, 1996, Chapter 8 (automata, traces and simulation relations).
