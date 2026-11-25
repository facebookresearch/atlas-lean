# A polling driver interrupted by a producer still simulates the sampled register

Take the [polling driver composed with the sampled register](polling-driver-simulates-the-sampled-register.md) and add a producer
interrupt handler that may run between any two steps of the driver. Its steps are internal steps on its own local state and
atomic $\mathsf{Publish}$ events, it performs no other register access, and it leaves the driver's local state unchanged. Then
erasing the internal steps of both the driver and the handler, and keeping the atomic $\mathsf{Publish}$ and $\mathsf{Read}$
steps in their order, maps every interleaved run to a trace of the
[sampled register](overwrite-register-reads-return-increasing-publications.md). Hence the samples the driver emits still have
strictly increasing publication numbers and carry the values of those publications.

## Depends on

- [A polling driver simulates the sampled-register specification](polling-driver-simulates-the-sampled-register.md)
- [Reads of an overwrite-newest register return increasing publications](overwrite-register-reads-return-increasing-publications.md)

## Sources

- H. Kopetz, *Real-Time Systems: Design Principles for Distributed Embedded Applications*, 2nd edition, Springer, 2011, Chapter 4 (state messages with update-in-place semantics).
- N. A. Lynch, *Distributed Algorithms*, Morgan Kaufmann, 1996, Chapter 8 (automata, traces and simulation relations).
