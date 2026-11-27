# Coverability is decidable for well-structured transition systems

Let $(S, \to, \le)$ be a [well-structured transition system](well-structured-transition-systems.md). It has *effective pred-basis* if an
algorithm maps each state $s$ to $\mathrm{pb}(s)$, a finite basis of the upward closure ${\uparrow}\mathrm{Pred}({\uparrow}s)$; this requires no strong
compatibility, because $\mathrm{pb}$ describes the upward closure of the one-step predecessors rather than the predecessors themselves.

- Every upward-closed set has a finite basis, and every increasing sequence $I_0 \subseteq I_1 \subseteq \cdots$ of upward-closed sets is
  eventually constant.
- If $I$ is upward closed, then $\mathrm{Pred}^*(I)$, the set of states from which $I$ is reachable, is upward closed.
- Given a finite basis $I^b$ of $I$, let $K_0 = I^b$ and $K_{n+1} = K_n \cup \mathrm{pb}(K_n)$. There is a least $m$ with ${\uparrow}K_m = {\uparrow}K_{m+1}$, and
  ${\uparrow}K_m = \bigcup_i {\uparrow}K_i = \mathrm{Pred}^*(I)$.

**Theorem.** If the system has effective pred-basis and $\le$ is decidable, a finite basis of $\mathrm{Pred}^*(I)$ is computable from a finite
basis of any upward-closed $I$, and the covering problem is decidable: $t$ can be covered from $s$ exactly when $s \in \mathrm{Pred}^*({\uparrow}t)$.

## Depends on

- [Well-structured transition systems](well-structured-transition-systems.md)

## Proof depends on

- [Well-structured transition systems](well-structured-transition-systems.md)

## Sources

- A. Finkel and Ph. Schnoebelen, "Well-structured transition systems everywhere!", *Theoretical Computer Science* 256(1–2):63–92, 2001: Lemmas 2.3 and 2.4, Proposition 3.1, Definition 3.2, Lemmas 3.3 and 3.4, Proposition 3.5 and Theorem 3.6.
