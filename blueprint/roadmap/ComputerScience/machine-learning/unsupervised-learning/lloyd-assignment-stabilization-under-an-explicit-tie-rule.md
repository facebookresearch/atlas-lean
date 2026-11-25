# Lloyd assignment stabilization under an explicit tie rule

This node collects the convergence behaviour of Lloyd's $k$-means iteration under explicit tie and
empty-cluster conventions.

## Expansion

A sound expansion has separate pages for:

1. **Conventions.** A deterministic rule for assigning points equidistant from several centres (for example the
   least index), and an empty-cluster policy (for example, an empty cluster keeps its previous centre).
2. **Assignment stabilization.** Under conventions that make the cost strictly decrease whenever the assignment
   changes (for example ties broken in favour of the current assignment), the assignments are eventually
   constant, since there are finitely many assignments.
3. Under other conventions the assignments can cycle at constant cost; that case is the cost-stabilization
   node.

## Proof depends on

- [Lloyd cost is eventually constant](lloyd-cost-is-eventually-constant.md)

## Sources

- A. Blum, J. Hopcroft and R. Kannan, *Foundations of Data Science* (2014 course draft): Lloyd's $k$-means algorithm and the fact that neither step increases the cost (p. 260 of that draft). <http://www.cs.cornell.edu/courses/cs4850/2014sp/book.pdf>
