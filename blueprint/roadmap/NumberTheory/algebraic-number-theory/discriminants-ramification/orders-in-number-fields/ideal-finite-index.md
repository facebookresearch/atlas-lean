# Nonzero ideals of an order have finite index

Let $K$ be a number field of degree
$n = [K : \mathbb{Q}]$, let $O$ be an order in $K$ (`NumberField.IsOrder`: a subring of $K$
contained in $\mathcal{O}_K$ with fraction field $K$; it is then a free $\mathbb{Z}$-module of
rank $n$, `NumberField.IsOrder.finrank_eq`), and let $\mathfrak{b}$ be a nonzero ideal of $O$.
Then:
1. $\mathfrak{b}$ contains a positive integer $m$;
2. the ring $O/\mathfrak{b}$ is finite, and its number of elements divides $m^n$ for every
   positive integer $m \in \mathfrak{b}$;
3. if $\mathfrak{b}$ is a prime ideal, it is a maximal ideal of $O$.

F. Keune, *Number Fields*, 2023, Lemma 3.17 with its proof (p. 57), proves (1) and (2) for
$O = \mathcal{O}_K$; A. V. Sutherland, MIT 18.783 Lecture 17 (Fall 2023), Definition 17.4
(p. 3), uses $[O : \mathfrak{a}] = \#(O/\mathfrak{a}) \in \mathbb{Z}_{>0}$ for a nonzero ideal of an
order.
