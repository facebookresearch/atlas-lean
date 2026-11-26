# Strata respect paths of the precedence graph

Let $P$ be a $\mathrm{datalog}^\neg$ program with stratification map $\sigma$, as on
[the stratification page](stratifications-and-the-precedence-graph.md). If there is a path from $R'$ to $R$ in the precedence
graph $G_P$, then $\sigma(R') \le \sigma(R)$; if some such path contains a negative edge, then $\sigma(R') < \sigma(R)$. In
particular a program whose precedence graph has a cycle through a negative edge has no stratification.

## Depends on

- [Stratifications and the precedence graph of a Datalog program with negation](stratifications-and-the-precedence-graph.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Lemma 15.2.6 (p. 380), proof omitted there, and its use in Proposition 15.2.7.
