# Reachability in Petri nets is decidable

There is an algorithm that decides, given a [Petri net](place-transition-petri-nets.md) $(N, M_0)$ and a marking $M$, whether $M$ is in the [reachability set](reachability-set-and-reachability-graph.md) $R(N, M_0)$. Mayr gave the first complete proof, Kosaraju a simpler one; all known algorithms of that period require non-primitive-recursive space.

## Depends on

- [Reachability set and reachability graph](reachability-set-and-reachability-graph.md)
- [Place/transition Petri nets](place-transition-petri-nets.md)

## Expansion

This page needs a decomposition before it can be stated with its proof prerequisites. A good expansion follows one complete proof, such as Mayr's or Kosaraju's, and adds a page for each of its main steps, with checked locators.

## Sources

- J. Esparza and M. Nielsen, "Decidability issues for Petri nets – a survey", BRICS Report Series RS-94-8, Aarhus University, 1994, <https://arxiv.org/abs/2411.01592>, Section 3, paragraph "Reachability" (Mayr's proof of 1981, Kosaraju's simplification, and the book-length account of the proof).
- J. Esparza, "Decidability and complexity of Petri net problems – an introduction", in *Lectures on Petri Nets I: Basic Models*, Lecture Notes in Computer Science 1491, Springer, 1998, pp. 374–428, <https://archive.model.in.tum.de/um/bibdb/esparza/course.pdf>, Section 8 (decidability by Mayr and Kosaraju and the gap to the exponential-space lower bound).
