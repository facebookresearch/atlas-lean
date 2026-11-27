# Lipton's exponential-space lower bound

There is a constant $d > 0$ such that neither the covering problem nor the boundedness problem for [vector addition systems](vector-addition-systems.md) of size $n$ can be decided in space $2^{d\sqrt{n}}$, even when every component of every vector in the addition set is $-1$, $0$ or $1$. The reachability problem for Petri nets also requires exponential space. So [Rackoff's upper bound](rackoff-s-exponential-space-bound.md) is close to optimal. The proof simulates a deterministic exponentially bounded automaton by a Petri net of polynomial size.

## Depends on

- [Vector addition systems](vector-addition-systems.md)
- [Reachability set and reachability graph](reachability-set-and-reachability-graph.md)

## Sources

- C. Rackoff, "The covering and boundedness problems for vector addition systems", *Theoretical Computer Science* 6:223–231, 1978, Section 2 and Remark 2.2 (statement of Lipton's lower bound in this formulation).
- J. Esparza, "Decidability and complexity of Petri net problems – an introduction", in *Lectures on Petri Nets I: Basic Models*, Lecture Notes in Computer Science 1491, Springer, 1998, pp. 374–428, <https://archive.model.in.tum.de/um/bibdb/esparza/course.pdf>, Section 7 ("A universal lower bound": Lipton's simulation of exponentially bounded automata by Petri nets, presented in detail).
- J. Esparza and M. Nielsen, "Decidability issues for Petri nets – a survey", BRICS Report Series RS-94-8, Aarhus University, 1994, <https://arxiv.org/abs/2411.01592>, Section 3, paragraphs "Boundedness" and "Reachability".
