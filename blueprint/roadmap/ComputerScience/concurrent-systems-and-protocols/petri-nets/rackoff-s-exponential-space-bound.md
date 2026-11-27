# Rackoff's exponential-space bound for covering and boundedness

There is a constant $c$ such that the covering problem and the boundedness problem for [vector addition systems](vector-addition-systems.md) can each be decided in space $2^{c n \log n}$, where $n$ is the size of the input. The key step bounds the length of witnesses: if $v_1 \in C(v, A)$, then some path from $v$ whose vectors all lie in $\mathbb{N}^k$ ends in a vector $w \ge v_1$ and has length at most $2^{2^{c n \log n}}$; and if $R(v, A)$ is infinite, then $(v, A)$ has a self-covering path, one whose last vector is $\ge$ some earlier vector and differs from it, whose vectors all lie in $\mathbb{N}^k$ and whose length is at most $2^{2^{c n \log n}}$. A nondeterministic search for such a path runs in exponential space, and Savitch's theorem makes it deterministic.

## Depends on

- [Vector addition systems](vector-addition-systems.md)

## Proof depends on

- [Unbounded vector addition systems have self-covering paths](unbounded-vector-addition-systems-have-self-covering-paths.md)

## Expansion

This page becomes ready once its proof prerequisites are linked:

- the bound on the shortest covering path, by induction on the number of coordinates that must stay nonnegative (Lemmas 3.3 and 3.4 and Theorem 3.5 of the source)
- the bound on the shortest self-covering path, which uses a bound on small integer solutions of linear systems due to Borosh and Treybig (Lemmas 4.3–4.7 and Theorem 4.8)
- Savitch's theorem in the form that a nondeterministic machine using space $s(n) \ge \log n$ can be simulated deterministically in space $O(s(n)^2)$ (proof prerequisite)

## Sources

- C. Rackoff, "The covering and boundedness problems for vector addition systems", *Theoretical Computer Science* 6:223–231, 1978: Theorem 3.5 (covering) and Theorem 4.8 (boundedness), with the length bounds of Sections 3 and 4.
- J. Esparza, "Decidability and complexity of Petri net problems – an introduction", in *Lectures on Petri Nets I: Basic Models*, Lecture Notes in Computer Science 1491, Springer, 1998, pp. 374–428, <https://archive.model.in.tum.de/um/bibdb/esparza/course.pdf>, Section 8 (Rackoff's upper bound for the covering and boundedness problems for Petri nets).
- J. Esparza and M. Nielsen, "Decidability issues for Petri nets – a survey", BRICS Report Series RS-94-8, Aarhus University, 1994, <https://arxiv.org/abs/2411.01592>, Section 3, paragraph "Boundedness" (a token generator of double exponential length and space $2^{c n \log n}$).
