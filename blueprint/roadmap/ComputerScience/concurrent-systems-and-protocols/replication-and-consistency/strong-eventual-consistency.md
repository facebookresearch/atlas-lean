# Strong eventual consistency

A replicated object is *eventually consistent* if every update delivered at some correct replica is eventually delivered at every correct replica, and whenever correct replicas have from some time on delivered the same updates, they are from some later time on in equivalent states; all methods terminate. It is *strongly eventually consistent* if moreover correct replicas that have delivered the same set of uniquely identified updates are in equivalent states immediately, without further coordination.

## Depends on

- [Infinite run](../../process-calculi/labelled-transition-systems/omega-run.md)

## Sources

- M. Shapiro, N. Preguiça, C. Baquero and M. Zawirski, "Conflict-free replicated data types", *SSS 2011*, LNCS 6976, Springer, 2011; INRIA research report RR-7687, Definitions 2.2 and 2.3
