# Molecular graphs under valence constraints

A molecular graph is a finite simple graph whose vertices carry atom types and whose edges carry a bond order in $\{1,2,3\}$. A constraint function assigns each atom type a bond budget, and the graph is admissible when no vertex spends more than its budget.

Fix a finite set $\mathcal{A}$ of atom types and a constraint function

$$
\nu \colon \mathcal{A} \to \mathbb{N}_0 , \qquad \mathbb{N}_0 = \mathbb{N} \cup \{0\} .
$$

A *molecular graph* over $\mathcal{A}$ is a triple $G = (V, E, \mathrm{type})$ with $V$ finite, $\mathrm{type} \colon V \to \mathcal{A}$, and $E$ a set of unordered pairs $\{u,v\}$, $u \neq v$, each pair carrying one bond order $d(\{u,v\}) \in \{1,2,3\}$. Two atoms are joined by at most one edge, whose order records the bond multiplicity; this is the model the ring-closure rule of this chapter updates, where an existing bond is promoted rather than duplicated. The *explicit degree* of a vertex is

$$
b(v) = \sum_{e \in E,\; v \in e} d(e) .
$$

The graph is *$\nu$-admissible* when

$$
b(v) \le \nu(\mathrm{type}(v)) \qquad \text{for every } v \in V .
$$

Three notions are kept apart. $\nu$-admissibility is the arithmetic condition just stated; chemical stability is not implied by it, and syntactic validity of a string that denotes the graph is a property of the string, not of the graph. Following the source's terminology, a SMILES string is *semantically valid* when it is syntactically valid and the graph it denotes is $\nu$-admissible.

Under a hydrogen convention in which a vertex of type $a$ may carry implicit hydrogen atoms, a $\nu$-admissible graph can be *saturated* by attaching $\nu(\mathrm{type}(v)) - b(v)$ hydrogen atoms to each $v$; the operation needs that convention and is not part of admissibility. A graph with no vertices is admissible for every $\nu$, and $\nu(a) = 0$ forces every vertex of type $a$ to be isolated. A constant $\nu \equiv c$ does not make the condition vacuous in general, since a star with more than $c$ leaves violates it; it is nonbinding only on graphs whose degrees stay below $c$.

The values $\nu(\mathrm{C}) = 4$, $\nu(\mathrm{N}) = 3$, $\nu(\mathrm{O}) = 2$, $\nu(\mathrm{F}) = 1$ are the plausible setting the source displays as an example, not a complete constraint table; the definition is parametric in $\nu$.

## Depends on

None.

## Proof depends on

None.

## Expansion

A formal development takes a finite vertex type, a type map into a finite atom-type universe, an edge set of unordered distinct pairs with an order function into $\{1,2,3\}$, and defines $b$ as a finite sum and admissibility as a bounded quantification. Saturation is a map defined on a hydrogen-carrying extension of the type universe; proving it well defined uses only $b(v) \le \nu(\mathrm{type}(v))$. A conversion from a multigraph model, in which parallel edges are summed into one order, is lossless only on multigraphs whose summed order per pair is at most three, and that restriction has to be stated wherever such a conversion is used.

## Context

Undergraduate foundation for chemical representations: the object that the string representations and generative models of this chapter are required to produce. Krenn, Lo, Pollice and Aspuru-Guzik state the valence condition in this form.

## Sources

- Alston Lo, Robert Pollice, AkshatKumar Nigam, Andrew D. White, Mario Krenn and Alán Aspuru-Guzik, *Recent advances in the Self-Referencing Embedded Strings (SELFIES) library*, Digital Discovery 2 (2023) 897–908, Section III (syntactic and semantic validity, the constraint function, and Eq. 1 as an example setting). DOI [10.1039/d3dd00044c](https://doi.org/10.1039/d3dd00044c), PMC10408573.
- Mario Krenn, Florian Häse, AkshatKumar Nigam, Pascal Friederich and Alán Aspuru-Guzik, *Self-referencing embedded strings (SELFIES): A 100% robust molecular string representation*, Machine Learning: Science and Technology 1 (2020) 045024, Section 1. DOI [10.1088/2632-2153/aba947](https://doi.org/10.1088/2632-2153/aba947).
