# Raney's cycle lemma

Let $a = (a_0, \dots, a_{n-1})$ be a list of integers, each at least
$-1$, whose entries sum to $-1$. Then there is exactly one index $r$ with $0 \le r < n$ such that
every proper prefix of the rotation $(a_r, \dots, a_{n-1}, a_0, \dots, a_{r-1})$ has nonnegative
sum: for every $t$ with $0 \le t < n$, the sum of the first $t$ entries of this rotation is at
least $0$.

The hypothesis that every entry is at least $-1$ is not needed; Raney's cycle lemma for arbitrary
integer lists proves the same conclusion without it.

## Sources

- Alexander M. Haupt, *Enumeration of $S$-omino Towers and Row-Convex $k$-omino Towers*, Journal of Integer
  Sequences 24 (2021), Article 21.3.6, Lemma 25 (a version of Raney's lemma, stated with indices from $1$),
  <https://cs.uwaterloo.ca/journals/JIS/VOL24/Haupt/haupt4.tex>.
