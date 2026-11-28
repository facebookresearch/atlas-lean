# Weak closure and weak realizability of sets of MSCs

A set of message sequence charts is weakly realizable when every chart that any distributed finite-state implementation accepting the set must also accept already belongs to the set.

Implementations are tuples of finite automata $A_1, \dots, A_n$, one per process, running asynchronously over FIFO buffers between all pairs of processes. A set $L$ of MSCs *weakly implies* an MSC $M$ if every tuple of automata whose product accepts all MSCs of $L$ also accepts $M$; equivalently, for every $i$ there is $M_i \in L$ whose events on $P_i$ form the same sequence as those of $M$. The *weak closure* $L^w$ is the set of MSCs weakly implied by $L$, and $L$, or a graph $G$ with $L(G) = L$, is *weakly realizable* if $L = L^w$.

## Depends on

- [MSC graphs](msc-graphs.md)

## Proof depends on

None.

## Expansion

Weak realizability does not require the implementation to be deadlock-free; safe realizability does. For a finite set of MSCs, weak realizability is coNP-complete and safe realizability is decidable in polynomial time; for bounded graphs safe realizability is in EXPSPACE.

## Sources

- Rajeev Alur, Kousha Etessami and Mihalis Yannakakis, "Realizability and verification of MSC graphs", *Theoretical Computer Science* 331(1):97–114, 2005, doi:10.1016/j.tcs.2004.09.034; read in the authors' open-access copy at <https://www.cis.upenn.edu/~alur/Icalp01.pdf>, which carries the journal text: Section 2.3 (concurrent automata) and Section 3.1 (weak implication, weak closure and weak realizability) of that copy.
