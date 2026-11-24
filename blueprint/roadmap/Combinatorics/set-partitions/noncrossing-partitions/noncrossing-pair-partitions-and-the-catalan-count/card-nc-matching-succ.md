# Catalan recursion for noncrossing matchings

Writing $M(n)$ for the number of noncrossing perfect matchings of $\{0, \dots, n-1\}$,

$$M(n + 1) = \sum_{j=0}^{n-1} M(j)\, M(n - 1 - j).$$

The point $0$ is matched to some $j + 1$ with $0 \le j < n$, and
[splitting off the arc](split-equiv.md) $\{0, j + 1\}$ leaves independent noncrossing matchings of
the $j$ points inside it and of the $n - 1 - j$ points to its right.

This is the recursion that Anderson, Guionnet and Zeitouni use for all noncrossing partitions
(cut at the largest element in the block of $1$), restricted to pairings.

## Informally uses

- [Splitting off the first arc](split-equiv.md): the bijection on each fibre $f(0) = j + 1$.

## Sources

- Greg W. Anderson, Alice Guionnet and Ofer Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010 (numbering of the authors' pre-publication manuscript (2009), https://www.math.nyu.edu/~zeitouni/cupbook.pdf), §2.1.1, the recursion $\gamma_k = \sum_{j=1}^{k} \gamma_{k-j}\gamma_{j-1}$
  for noncrossing partitions after Definition 2.1.4.
