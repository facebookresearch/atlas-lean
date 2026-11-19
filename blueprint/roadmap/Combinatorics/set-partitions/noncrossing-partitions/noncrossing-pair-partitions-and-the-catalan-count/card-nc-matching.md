# Counting noncrossing perfect matchings

The number of noncrossing perfect matchings of $\{0, \dots, n-1\}$ is $C_{n/2}$ when $n$ is even
and $0$ when $n$ is odd; in particular there is exactly one (empty) matching of the empty set.

Proof: by strong induction from the
[Catalan recursion](card-nc-matching-succ.md). For $n + 1 = 2k + 1$ odd, in each term
$M(j)M(2k - 1 - j)$ one of $j$ and $2k - 1 - j$ is odd, so the sum vanishes. For $n + 1 = 2k + 2$,
only even $j = 2a$ contribute, giving $\sum_{a=0}^{k} C_a C_{k-a} = C_{k+1}$, Segner's recursion
for the Catalan numbers.

## Informally uses

- [Catalan recursion for noncrossing matchings](card-nc-matching-succ.md): the recursion the
  induction runs on.
- [Catalan numbers](../../../catalan-numbers-lattice-paths/catalan-numbers/catalan-numbers/README.md):
  the recursion $C_{k+1} = \sum_{a=0}^{k} C_a C_{k-a}$ with $C_0 = 1$.
