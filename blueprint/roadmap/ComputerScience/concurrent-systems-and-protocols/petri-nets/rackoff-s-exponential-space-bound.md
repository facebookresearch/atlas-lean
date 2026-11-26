# Rackoff's exponential-space bound for covering and boundedness

There is a constant $c$ such that the covering problem and the boundedness problem for [vector addition systems](vector-addition-systems.md) can each be decided in space $2^{c n \log n}$, where $n$ is the size of the input. The key step bounds the length of witnesses: if $v_1$ is covered from $v$, it is covered along a path of length at most $2^{2^{c n \log n}}$, and a system with an infinite reachability set has a self-covering path of length at most $2^{2^{c n \log n}}$; a nondeterministic search for such a path runs in exponential space, and Savitch's theorem makes it deterministic.

## Depends on

- [Vector addition systems](vector-addition-systems.md)

## Sources

- C. Rackoff, "The covering and boundedness problems for vector addition systems", *Theoretical Computer Science* 6:223–231, 1978: Theorem 3.5 (covering) and Theorem 4.8 (boundedness), with the length bounds of Sections 3 and 4.
- J. Esparza, "Decidability and complexity of Petri net problems – an introduction", in *Lectures on Petri Nets I: Basic Models*, Lecture Notes in Computer Science 1491, Springer, 1998, pp. 374–428, <https://archive.model.in.tum.de/um/bibdb/esparza/course.pdf>, Section 8 (Rackoff's upper bound for the covering and boundedness problems for Petri nets).
- J. Esparza and M. Nielsen, "Decidability issues for Petri nets – a survey", BRICS Report Series RS-94-8, Aarhus University, 1994, <https://arxiv.org/abs/2411.01592>, Section 3, paragraph "Boundedness" (a token generator of double exponential length and space $2^{c n \log n}$).
