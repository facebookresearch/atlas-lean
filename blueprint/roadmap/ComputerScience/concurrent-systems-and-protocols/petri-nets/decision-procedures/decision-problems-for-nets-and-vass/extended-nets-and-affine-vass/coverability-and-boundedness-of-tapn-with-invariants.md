# Coverability and boundedness of timed-arc Petri nets with invariants are undecidable

Timed-arc Petri nets give each token a real-valued age and guard arcs with age intervals; boundedness and coverability are decidable for them. Adding age invariants on places, as the tool TAPAAL does to model urgency, makes both problems undecidable.

**Setting (Jacobsen, Jacobsen and Møller).** Intervals are $[a, a]$, $[a, b]$, $[a, b)$, $(a, b]$, $(a, b)$, $[a, \infty)$, $(a, \infty)$ with $a \in \mathbb{N}_0$, $b \in \mathbb{N}$, $a < b$; invariant intervals are $[0, 0]$, $[0, b]$, $[0, b)$, $[0, \infty)$. A *timed-arc Petri net with invariants* (ITAPN) is $N = (P, T, F, c, \iota)$ with finite disjoint sets of places $P$ and transitions $T$, a flow relation $F \subseteq (P \times T) \cup (T \times P)$, an interval $c(p, t)$ on each input arc and an invariant interval $\iota(p)$ on each place. A *marking* assigns to each place a finite multiset of nonnegative real token ages lying in its invariant; initial markings have all ages $0$. A transition is enabled if each input place holds a token whose age lies in the arc's interval; firing removes one such token from each input place and adds a token of age $0$ to each output place. A delay $d \ge 0$ is allowed if all aged tokens $x + d$ still satisfy their places' invariants, and it adds $d$ to every age. A marked net is *bounded* if, for some $k$, no reachable marking has more than $k$ tokens in a place. A marking $M$ is *coverable* if some reachable marking $M'$ satisfies $M'(p) \supseteq M(p)$ for every place $p$, as multisets of ages.

**Theorem (Jacobsen, Jacobsen and Møller).** The boundedness problem (given a marked ITAPN, is it bounded?) and the coverability problem (given a marked ITAPN and a marking, is the marking coverable?) are undecidable for ITAPN.

For timed-arc Petri nets without invariants reachability is undecidable, while boundedness and coverability are decidable.

## Depends on

- [Place/transition Petri nets](../../../place-transition-petri-nets.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction weakly simulates a two-counter Minsky machine: register $r_i$ is a place whose number of tokens is the counter value, with invariant $\le 1$, and each instruction is a small net in which register tokens are reset to age $0$ and a token is added to a place $p_{\mathit{count}}$. The net can cheat, for example by taking a zero-test branch while the register is nonempty, but then a register keeps a token of nonzero age; because increments, halting and the else-branch of a test each need a delay of one time unit, the invariant then blocks them, and the net can perform at most $v_1 + v_2$ further decrements before getting stuck. Hence the machine halts if and only if the net is bounded (non-halting runs put unboundedly many tokens on $p_{\mathit{count}}$), and if and only if the marking with a single age-$0$ token on the halting place is coverable.

## Sources

- Lasse Jacobsen, Morten Jacobsen and Mikael H. Møller, "Undecidability of Coverability and Boundedness for Timed-Arc Petri Nets with Invariants", Mathematical and Engineering Methods in Computer Science (MEMICS 2009), OpenAccess Series in Informatics (OASIcs) 13, 2009, pp. 106–113, <https://doi.org/10.4230/DROPS.MEMICS.2009.2346>; Definitions 1–4, Problems 1 and 2, Lemmas 1–3, Theorems 2 and 3 and the summary table of the conclusion, read in the open-access copy at <https://drops.dagstuhl.de/storage/01oasics/oasics-vol013-memics2009/DROPS.MEMICS.2009.2346/DROPS.MEMICS.2009.2346.pdf>.
