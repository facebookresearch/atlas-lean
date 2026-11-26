# Suspect forwarding transforms weak completeness into strong completeness

If each process periodically broadcasts its local detector's suspect set and, upon receiving $(q, \mathit{suspects}_q)$, updates its output to $(\mathit{output} \cup \mathit{suspects}_q) \setminus \{q\}$, then under fair asynchronous delivery among correct processes the emulated detector satisfies strong completeness whenever the underlying one is weakly complete, and it preserves strong, weak, eventual strong and eventual weak accuracy. Hence $\mathcal Q \to \mathcal P$, $\mathcal W \to \mathcal S$, $\Diamond\mathcal Q \to \Diamond\mathcal P$ and $\Diamond\mathcal W \to \Diamond\mathcal S$.

## Proof sketch

A crashed process stops broadcasting and so is never removed from outputs once some correct process suspects it permanently; forwarding spreads that suspicion to all correct processes. A correct process removes itself from others' outputs each time it broadcasts, so accuracy is preserved.

## Depends on

- [Failure detector classes](../failure-detector-classes.md)
- [Asynchronous message-passing systems](../../distributed-execution-models/asynchronous-message-passing-systems.md)

## Proof depends on

- [Inclusions and separations among the Chandra–Toueg failure detector classes](inclusions-and-separations-among-the-chandra-toueg-failure-detector-classes.md)

## Sources

- Tushar Deepak Chandra and Sam Toueg, "Unreliable Failure Detectors for Reliable Distributed Systems", Journal of the ACM, 1996.
