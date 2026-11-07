# Recurrence for the area distribution by first letter

For natural numbers $m$, $j$ and
$\ell$, let $c(m, j, \ell; q) \in \mathbb{Z}[q]$ be the area distribution of the words of length
$m$ with letters in $\{1, \dots, j\}$, each letter at most one more than the letter before it,
that begin with $\ell$ and end with $j$. For all natural numbers $m \ge 2$ and $j$, $\ell$ with
$1 \le \ell \le j$,

$$c(m, j, \ell; q) = q^{\ell} \sum_{i=1}^{\ell+1} c(m-1, j, i; q),$$

and $c(1, j, \ell; q)$ equals $q^{\ell}$ if $j = \ell$ and $0$ otherwise.

## Sources

- Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 1 (`integers-2025-A5-lem-1`).
