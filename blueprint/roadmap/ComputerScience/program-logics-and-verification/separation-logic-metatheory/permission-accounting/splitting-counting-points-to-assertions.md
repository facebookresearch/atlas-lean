# Splitting and joining counting points-to assertions

With counting permissions, a source with $n$ read permissions outstanding splits into a read token of size $m$ and a source with $n + m$ outstanding, and back; read tokens split and merge by adding their sizes; and a total permission for an address excludes every other permission for it.

Work with heaps over the counting permission model $(\mathbb{Z}, \star_1)$ of [fractional and counting permission models](fractional-and-counting-permission-models.md). For expressions $E, E'$ and integers $n, m$, at every store and heap,

$$E \overset{n}{\mapsto} E' \iff E \overset{n+m}{\longmapsto} E' \ast E \overset{-m}{\longmapsto} E' \qquad (n \ge 0,\ m > 0),$$

$$E \overset{-(n+m)}{\longmapsto} E' \iff E \overset{-n}{\longmapsto} E' \ast E \overset{-m}{\longmapsto} E' \qquad (n, m > 0),$$

$$E \overset{0}{\mapsto} E' \ast E \overset{n}{\mapsto} E' \iff \mathrm{false} \qquad (n \in \mathbb{Z}),$$

and two sources for one address never coexist: $E \overset{n}{\mapsto} E' \ast E \overset{n'}{\mapsto} E'$ is false for $n, n' \ge 0$.

In the combined model $(\mathbb{Q}, \star_3)$ the first two laws hold verbatim for rationals, $q \ge 0$ and $q' > 0$ in the first and $q, q' > 0$ in the second, so read permissions can also be divided.

## Depends on

- [Fractional and counting permission models](fractional-and-counting-permission-models.md)
- [Permission algebras and heaps with permissions](permission-models.md)

## Proof depends on

- [Fractional and counting permission models](fractional-and-counting-permission-models.md)
- [Permission algebras and heaps with permissions](permission-models.md)

## Expansion

All four laws reduce, as for fractions, to definedness of the combination of two one-cell heaps at one address with one value. For $n \ge 0$ and $m > 0$, $(n + m) \star_1 (-m)$ is defined, since one argument is negative and the sum $n$ is nonnegative, and equals $n$. For $n, m > 0$, $(-n) \star_1 (-m) = -(n + m)$, both arguments being negative. The total permission $0$ combines with nothing, and two nonnegative permissions never combine. With tokens of size one the laws are the permission manipulations of a reader–writer lock: a reader takes a token $-1$ from the source and returns it, and the writer can regain the total permission $0$ only when every token has been returned.

## Sources

- R. Bornat, C. Calcagno, P. O'Hearn and M. Parkinson, "Permission accounting in separation logic", *Proceedings of the 32nd ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL 2005)*, ACM, 2005, pp. 259–270, <https://doi.org/10.1145/1040305.1040327>, author copy <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/permissions_paper.pdf>, Section 8, equation (10); Section 10.2, equation (16); Section 10.4, equation (18).
- R. Dockins, A. Hobor and A. W. Appel, "A fresh look at separation algebras and share accounting", *Programming Languages and Systems (APLAS 2009)*, LNCS 5904, Springer, 2009, pp. 161–177, <https://doi.org/10.1007/978-3-642-10672-9_13>, author copy dated June 2009 <https://www.cs.princeton.edu/~appel/papers/fresh-sa.pdf>, Section 6, Definition 9 and equations (39)–(41) (equation numbers of the author copy).
