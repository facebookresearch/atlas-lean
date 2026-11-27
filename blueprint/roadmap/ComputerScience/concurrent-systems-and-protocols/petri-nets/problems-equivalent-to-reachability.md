# Problems recursively equivalent to Petri-net reachability

Each of the following problems for [Petri nets](place-transition-petri-nets.md) is recursively equivalent to the [reachability problem](reachability-set-and-reachability-graph.md):

- the *submarking reachability problem*: given a partial marking that fixes the number of tokens on some places, is some reachable marking equal to it on those places;
- the *zero reachability problem*: is the marking with no tokens reachable;
- the *single-place zero reachability problem*: given a place $s$, is some reachable marking $M$ with $M(s) = 0$;
- the *liveness problem*: is the net [live](liveness-and-deadlock-freedom.md).

## Depends on

- [Reachability set and reachability graph](reachability-set-and-reachability-graph.md)
- [Liveness and deadlock-freedom of Petri nets](liveness-and-deadlock-freedom.md)
- [Place/transition Petri nets](place-transition-petri-nets.md)

## Sources

- J. Esparza and M. Nielsen, "Decidability issues for Petri nets – a survey", BRICS Report Series RS-94-8, Aarhus University, 1994, read in the report version reposted at <https://arxiv.org/abs/2411.01592>, Section 3 of that version, paragraphs "Reachability" (Hack's results on the submarking, zero and single-place zero reachability problems) and "Liveness" (Hack's equivalence of liveness and reachability).
