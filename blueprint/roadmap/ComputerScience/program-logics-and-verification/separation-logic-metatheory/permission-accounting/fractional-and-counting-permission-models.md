# Fractional and counting permission models

Fractional permissions are the rationals in $(0, 1]$, added while the sum stays at most $1$, with $1$ the write permission. Counting permissions are integers: $0$ is the total permission, a positive $k$ is a source from which $k$ read permissions have been split off, and a negative $-k$ is $k$ read permissions held together.

Each of the following is a set of permissions with a partial, commutative and associative operation and a named write permission, over which heaps are built as in [permission algebras and heaps with permissions](permission-models.md).

1. *Fractional permissions.* $M = \{q \in \mathbb{Q} : 0 < q \le 1\}$, with $q \star_2 q' = q + q'$ if $q + q' \le 1$ and undefined if $q + q' > 1$. The write permission is $1$; every $q < 1$ grants read access only. The interval $(0, 1]$ of rational numbers, with the operation being addition but undefined when permissions add up to more than $1$, is a permission algebra in the sense of [permission algebras and heaps with permissions](permission-models.md).
2. *Counting permissions.* $M = \mathbb{Z}$, with

$$i \star_1 j = \begin{cases} \text{undefined} & \text{if } i \ge 0 \text{ and } j \ge 0, \\ \text{undefined} & \text{if } (i \ge 0 \text{ or } j \ge 0) \text{ and } i + j < 0, \\ i + j & \text{otherwise.} \end{cases}$$

   The write permission is $0$; $-1$ is a single read permission, $k > 0$ is a source from which $k$ read permissions have been taken, and $-k$ with $k > 0$ is $k$ read permissions held together. Two sources never combine, and a source never absorbs more read permissions than it has issued.
3. *Combined permissions.* $M = \mathbb{Q}$, with $\star_3$ given by the same three clauses as $\star_1$ for rationals $i, j$. The write permission is $0$, and read permissions $-q$ with $q > 0$ are divisible.

In each model only the write permission allows mutation and disposal, and any permission allows lookup.

With a unit added, the first two become separation algebras of shares: *fractional shares* $[0, 1] \cap \mathbb{Q}$ under addition defined when the sum is at most $1$, with unit $0$; and *counting shares* $\mathbb{Z} \cup \{\bot\}$ with unit $\bot$, where integers $x, y$ join to $x + y$ exactly when ($x < 0$ or $y < 0$) and ($x + y \ge 0$ or both $x < 0$ and $y < 0$), the same definedness condition as $\star_1$.

## Depends on

- [Permission algebras and heaps with permissions](permission-models.md)

## Proof depends on

None.

## Expansion

Each write permission combines with nothing: $1 \star_2 q$ is undefined since $1 + q > 1$, and $0 \star_1 j$ is undefined both for $j \ge 0$ (two nonnegative arguments) and for $j < 0$ (a nonnegative argument and a negative sum); the same holds for $\star_3$. Commutativity is evident, and associativity in the partial sense is a case analysis on signs in which each defined side is a sum. The fractional permissions $(0, 1]$ and the counting permissions $\mathbb{Z}$ are the non-unit elements of these share models, which is how heaps over them become separation algebras ([permission algebras and heaps with permissions](permission-models.md)); the classification of the share models by positivity and disjointness is on [positivity, disjointness and cross-split](positivity-disjointness-and-cross-split.md). The fractional scheme is Boyland's, as the permission-accounting paper says; the counting model mirrors permission counting in reader–writer protocols, and the combined model joins proliferation and divisibility of read permissions in one asymmetric model.

## Sources

- R. Bornat, C. Calcagno, P. O'Hearn and M. Parkinson, "Permission accounting in separation logic", *Proceedings of the 32nd ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL 2005)*, ACM, 2005, pp. 259–270, <https://doi.org/10.1145/1040305.1040327>, author copy <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/permissions_paper.pdf>, Section 7 (Boyland's numerical scheme), Section 8 (source and read permissions), Sections 10.1–10.4 (the partial commutative semigroup structure; the models $(\mathbb{Z}, \star_1)$, fractions with $\star_2$ and $(\mathbb{Q}, \star_3)$ with their write permissions).
- R. Dockins, A. Hobor and A. W. Appel, "A fresh look at separation algebras and share accounting", *Programming Languages and Systems (APLAS 2009)*, LNCS 5904, Springer, 2009, pp. 161–177, <https://doi.org/10.1007/978-3-642-10672-9_13>, author copy dated June 2009 <https://www.cs.princeton.edu/~appel/papers/fresh-sa.pdf>, Section 6, Definitions 8 and 9, equations (36)–(38) and the remarks after each definition (positive, not disjoint).
- C. Calcagno, P. W. O'Hearn and H. Yang, "Local action and abstract separation logic", *Proceedings of the 22nd Annual IEEE Symposium on Logic in Computer Science (LICS 2007)*, IEEE, 2007, pp. 366–378, <https://doi.org/10.1109/LICS.2007.30>, author copy <https://www.cs.ox.ac.uk/people/hongseok.yang/paper/asl-short.pdf>, Section 2, example 2 after Definition 1 (the interval $(0, 1]$ of rational numbers as a permission algebra).
