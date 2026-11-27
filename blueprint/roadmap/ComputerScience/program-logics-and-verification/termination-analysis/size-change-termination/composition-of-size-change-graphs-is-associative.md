# Composition of size-change graphs is associative

Let $G_1 : f \to g$, $G_2 : g \to h$ and $G_3 : h \to k$ be [size-change graphs](size-change-graphs.md), and let $G ; G'$ be their composition: it has an edge $x \xrightarrow{\downarrow} z$ if there are $y$ and edges $x \xrightarrow{r} y$ in $G$ and $y \xrightarrow{r'} z$ in $G'$ with at least one of $r, r'$ equal to $\downarrow$, and an edge $x \xrightarrow{\overline{\downarrow}} z$ if there are such edges but none of these two-edge paths contains a $\downarrow$ edge. Then

$$G_1 ; (G_2 ; G_3) = (G_1 ; G_2) ; G_3 .$$

## Depends on

- [Size-change graphs and size-change termination](size-change-graphs.md)

## Sources

- P. M. Neergaard, *The Size-Change Principle of Termination*, lecture notes, Brandeis University, <https://www.cs.brandeis.edu/~cs117a/size-change-termination.pdf>, Section 5, Definition 5.1 and Exercise 5.2.
