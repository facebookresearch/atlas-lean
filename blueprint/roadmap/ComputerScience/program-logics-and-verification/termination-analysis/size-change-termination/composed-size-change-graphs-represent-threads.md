# Composed size-change graphs represent threads

Let $M = G_1 \cdots G_n$ be a finite multipath of [size-change graphs](size-change-graphs.md) $G_i : f_{i-1} \to f_i$, let $x$ be a parameter of $f_0$ and $y$ a parameter of $f_n$, and let $G_1 ; \dots ; G_n$ be the [composition](composition-of-size-change-graphs-is-associative.md). Then $M$ has a thread from $x$ to $y$ over its entire length containing at least one $\downarrow$-labelled edge if and only if $x \xrightarrow{\downarrow} y$ is an edge of $G_1 ; \dots ; G_n$. Moreover, $M$ has a thread from $x$ to $y$ over its entire length if and only if $G_1 ; \dots ; G_n$ has an edge from $x$ to $y$ with either label.

## Depends on

- [Size-change graphs and size-change termination](size-change-graphs.md)
- [Composition of size-change graphs is associative](composition-of-size-change-graphs-is-associative.md)

## Sources

- P. M. Neergaard, *The Size-Change Principle of Termination*, lecture notes, Brandeis University, <https://www.cs.brandeis.edu/~cs117a/size-change-termination.pdf>, Section 5, Lemma 5.5 and its proof (by induction on $n$).
