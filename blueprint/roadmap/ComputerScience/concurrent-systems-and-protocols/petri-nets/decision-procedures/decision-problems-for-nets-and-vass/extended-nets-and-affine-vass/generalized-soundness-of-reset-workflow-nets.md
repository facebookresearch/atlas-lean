# Generalized soundness of reset workflow nets is undecidable

A workflow net is generalized sound if, from any number $k$ of tokens in its initial place, every reachable marking can still be completed to $k$ tokens in its final place. For workflow nets with reset arcs this property is undecidable, which completes the undecidability of all usual soundness variants for them.

**Setting (Blondin, Finkel, Hofman, Mazowiecki and Offtermatt).** A *reset Petri net* $(P, T, F, R)$ is an ordinary [Petri net](../../../place-transition-petri-nets.md) $(P, T, F)$, with flow relation $F \subseteq (P \times T) \cup (T \times P)$ and all arcs of weight $1$ (Section 2.2 of the source), together with reset arcs $R \subseteq T \times P$; firing $t$ consumes and produces tokens along $F$ as usual and empties every place $p$ with $(t, p) \in R$. A *reset workflow net* $(P, T, F, R, i, f)$ adds an initial place $i$ with no incoming arcs and a final place $f$ with no outgoing arcs and not reset by any transition, such that every place and transition lies on a path from $i$ to $f$ in the graph of the arcs of $F$. For $k \ge 1$, the net is *$k$-sound* if every marking reachable from $\{i : k\}$ ($k$ tokens in $i$, none elsewhere) can reach $\{f : k\}$; it is *generalized sound* if it is $k$-sound for every $k \ge 1$.

**Theorem (Blondin, Finkel, Hofman, Mazowiecki and Offtermatt).** The generalized soundness problem for reset workflow nets is undecidable.

The other soundness variants ($1$-soundness, $k$-soundness, structural soundness and classical soundness) were already known to be undecidable for reset workflow nets (van der Aalst, van Hee, ter Hofstede, Sidorova, Verbeek, Voorhoeve and Wynn). Without resets, generalized soundness is PSPACE-complete. The same paper identifies a decidable "$1$-in-between soundness" property implied by generalized soundness and implying $1$-soundness.

## Depends on

- [Place/transition Petri nets](../../../place-transition-petri-nets.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction is from control-state reachability $q_{\mathrm{src}}(\vec 0) \to^\ast q_{\mathrm{tgt}}(\vec 0)$ in two-counter Minsky machines. Each counter $x_i$ is a place with a budget place $\bar x_i$: an increment of $x_i$ decrements $\bar x_i$ and conversely, and a zero test becomes a reset of $x_i$, so a reset applied to a nonempty counter loses tokens from $\{x_i, \bar x_i\}$ for good. Starting the net with budget $k$ simulates exactly the runs whose counters stay within $[0, k]$. Three extra transitions with reset arcs connect this net to the places $i$ and $f$: one sets up the control state and a budget taken from the tokens in $i$, one can always clean up and move to $f$, and one, enabled at $q_{\mathrm{tgt}}$, resets the counters while keeping the budget. The resulting workflow net is generalized sound if and only if $q_{\mathrm{tgt}}(\vec 0)$ is not reachable from $q_{\mathrm{src}}(\vec 0)$.

## Sources

- Michael Blondin, Alain Finkel, Piotr Hofman, Filip Mazowiecki and Philip Offtermatt, "Soundness of reset workflow nets", in *Proceedings of the 39th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2024)*, ACM, 2024, pp. 1–14, doi:[10.1145/3661814.3662086](https://doi.org/10.1145/3661814.3662086); read in arXiv:2503.04440v1 ([arXiv](https://arxiv.org/abs/2503.04440v1)), cited by section: Section 1 (the earlier undecidability of the other soundness variants), Section 2 (reset Petri nets, reset workflow nets, $k$-soundness and generalized soundness), Section 3 (the undecidability theorem, Theorem 3.1, the simulation of Minsky machines with budget places and the workflow construction) and Section 4 ($1$-in-between soundness).
