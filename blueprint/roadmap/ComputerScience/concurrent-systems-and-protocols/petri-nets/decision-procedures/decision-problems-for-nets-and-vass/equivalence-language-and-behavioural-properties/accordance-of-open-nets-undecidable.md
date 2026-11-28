# Accordance of open nets with unbounded message queues is undecidable

An open net is a Petri net with input and output places through which it communicates asynchronously with its environment. One open net accords with another if it can replace it without breaking a behavioral property of the overall system. Without an a priori bound on pending messages, accordance is undecidable for deadlock freedom, responsiveness and weak termination.

**Setting (Müller, Stahl and Vogler).** A net $(P, T, F, m_N, \Omega)$ has finite disjoint sets of places and transitions, a flow relation $F \subseteq (P \times T) \cup (T \times P)$, an initial marking $m_N$ and a set $\Omega$ of final markings. An *open net* $(P, T, F, m_N, I, O, \Omega)$ adds disjoint sets of input places $I$ (with empty presets) and output places $O$ (with empty postsets), unmarked initially and in final markings; interface places are unbounded message buffers. Two open nets are *interface-equivalent* if they have the same input and output places, and *composable* if they communicate bilaterally and directedly through shared interface places; their composition $N_1 \oplus N_2$ merges the shared places. For the closed composition, a marking is *dead* if no transition is enabled, and *f-dead* if additionally it is not final; it is *responsive* if a transition producing on a former interface place can be enabled from it, *weakly terminating* if a final marking is reachable, and *f-responsive* if responsive or weakly terminating. $N_1$ and $N_2$ are deadlock free (f-deadlock free, responsive, f-responsive, weakly terminating) if $N_1 \oplus N_2$ is closed and every reachable marking is not dead (not f-dead, responsive, f-responsive, weakly terminating). For $x \in \{\mathit{df}, \mathit{fdf}, r, \mathit{fr}, \mathit{wt}\}$, an open net $C$ is an *$x$-controller* of $N$ if $N$ and $C$ have property $x$, and $\mathit{Impl}$ *$x$-accords* with an interface-equivalent $\mathit{Spec}$ if every $x$-controller of $\mathit{Spec}$ is an $x$-controller of $\mathit{Impl}$.

**Theorem (Müller, Stahl and Vogler).** For interface-equivalent open nets $\mathit{Impl}$ and $\mathit{Spec}$, $x$-accordance is undecidable for each $x \in \{\mathit{df}, \mathit{fdf}, r, \mathit{fr}, \mathit{wt}\}$. Moreover, the coarsest precongruences contained in $r$-accordance and in $\mathit{fr}$-accordance are undecidable.

Accordance for deadlock freedom and for responsiveness is decidable when a bound on the number of pending messages is known in advance.

## Depends on

- [Place/transition Petri nets](../../../place-transition-petri-nets.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

For deadlock freedom and responsiveness, the authors reduce from the halting problem of two-counter machines. From a machine they build two labeled nets that weakly simulate it, with "cheating" transitions that can fire wrongly at a zero test, and turn them into open nets by making visible actions interface places. Using trace-based characterizations of accordance (stop-dead semantics for deadlock freedom, a variant for responsiveness, and impossible futures for the precongruences), the two nets accord exactly when the machine does not halt. For weak termination they reduce from the undecidable question whether an open net has a weakly terminating controller: a net with no final markings has no such controller, and it accords with a given net $N$ exactly when $N$ has none.

## Sources

- Richard Müller, Christian Stahl and Walter Vogler, "Undecidability of accordance for open systems with unbounded message queues", Information Processing Letters 114(12), pp. 663–669, 2014, <https://doi.org/10.1016/j.ipl.2014.07.010>; Definitions 1–8 and Theorems 15, 19, 22 and 23 of the preprint version, read in the open-access copy at <https://pure.tue.nl/ws/files/3837857/585319286671463.pdf>.
