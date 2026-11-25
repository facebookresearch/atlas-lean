# Frame invariants of IC3

Let $(I, T)$ be a finite transition system and $P$ a set of safe states. Assume $I \subseteq P$ and $\mathrm{Img}_T(I) \subseteq P$; IC3 first checks both and reports a counterexample of length $0$ or $1$ if either fails. IC3 then maintains a sequence of state sets (frames) $F_0, \dots, F_k$, and each of its rules (strengthening a frame by a clause blocking a predecessor of a bad state, propagating clauses forward, and adding a new frame) preserves the invariants: $F_0 = I$; $F_i \subseteq F_{i+1}$; $F_i \subseteq P$ for $i < k$; and $\mathrm{Img}_T(F_i) \subseteq F_{i+1}$. If $F_i = F_{i+1}$ for some $i < k$, then $F_i$ is an inductive invariant contained in $P$, so every reachable state is safe.

## Proof depends on

- [Safety by inductive invariants](safety-by-inductive-invariants.md)

## Sources

- A. R. Bradley, "SAT-based model checking without unrolling", *VMCAI 2011*, LNCS 6538, Springer, 2011
