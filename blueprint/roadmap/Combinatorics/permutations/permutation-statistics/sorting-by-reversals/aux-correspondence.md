# Directed gaps of a partial signed permutation equal its doubled gaps

Let $n$ be a natural number and $(x, y_1, \dots, y_r)$, with $r \ge 0$, a nonempty list of
integers whose entries have absolute values between $1$ and $n$, pairwise distinct (a partial
signed permutation of $1, \dots, n$). Then the [directed gap count](dir-gap-count.md) of
$(x, y_1, \dots, y_r, n + 1)$ equals the [gap count](gap-count.md) of the list formed by the
second entry $\delta_2(x)$ of the [doubled pair](dbl-one.md) of $x$, then the
[doubled list](dbl.md) $\delta(y_1) \cdots \delta(y_r)$, then $2n + 1$:
$\vec g(x, y_1, \dots, y_r, n + 1) = g(\delta_2(x), \delta(y_1), \dots, \delta(y_r), 2n + 1)$,
where each $\delta(y_t)$ stands for its two entries. Adjacent signed entries match the
[junctions of their doubled pairs](between-gap.md), the inside of a doubled pair is
[never a gap](inside-gap.md), and the last pair matches at the [right end](right-gap.md). With
the left end added, this gives the
[equality of signed and doubled breakpoint counts](sbreaks-eq-ubreaks-dbl-of-valid.md) for
signed permutations (Shamir and Peer, Lecture 11, signed setting).
