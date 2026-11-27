# Possible-answer membership over Codd tables is NP-complete

For a positive existential query $q$, the possible-answer membership problem over Codd tables asks, given a Codd
table $T$ and a complete instance $I$, whether $I \in q(\mathrm{rep}(T))$. There is a positive existential query $q$
for which this problem is NP-complete; hardness is by reduction from graph 3-colorability, with the colors of the
endpoints of each edge stored as variables of the table. For every query evaluable in polynomial time on complete
databases, possible-answer membership over c-tables is in NP.

## Depends on

- [Conditional tables](conditional-tables.md)
- [Relational calculus and domain independence](../relational-calculus/relational-calculus-and-domain-independence.md)
- [NP-complete decision problems](../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

- [3-COLOR is NP-hard](../../../TheoryOfComputation/np-completeness/graph-coloring-and-partitioning/graph-3-coloring/part-09/col3-dec-np-hard.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, the problems of Section 19.4 and Proposition 19.4.1 with its proof (pp. 499–500).
