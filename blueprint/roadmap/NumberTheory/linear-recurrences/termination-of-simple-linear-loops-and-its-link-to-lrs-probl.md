# Termination of simple linear loops and its link to LRS problems

Let $M$ be an integer $k \times k$ matrix, $c \in \mathbb{Z}^k$, and consider the loop "while $c^{\mathsf T} x > 0$ do $x := Mx$" on
integer vectors. For an input $x$, the loop terminates if and only if $c^{\mathsf T} M^n x \le 0$ for some $n \ge 0$, that is, if and only if
the integer sequence $u_n = c^{\mathsf T} M^n x$ is not strictly positive. Since the terms are integers, strict positivity of $(u_n)$
is equivalent to non-strict positivity of $(u_n - 1)$, a linear recurrence sequence of order at most $k + 1$; so deciding
termination on a given input is equivalent to the complement of a positivity problem. For rational $M$, $c$ and $x$ the loop
terminates on $x$ if and only if $c^{\mathsf T} M^n x$ is not strictly positive, a strict positivity question. Guards that are equalities lead to
Skolem-type problems. Statements about the decidability status of these problems are made only as of a named
source.

## Proof

The order bound follows from the Cayley–Hamilton theorem for $M$ and the factor
$t - 1$ for the constant sequence.

## Depends on

- [Skolem, positivity and bounded reachability problems for LRS](skolem-positivity-and-bounded-reachability-problems-for-lrs.md)

## Proof depends on

- [Linear recurrence sequences as observations of companion-matrix dynamics](remaining-clauses-of-linear-recurrence-sequences-as-observed.md)

## Sources

- The Skolem Landscape (Invited Talk) — J. Worrell, ICALP 2023, LIPIcs 261, 5:1-5:2, DOI 10.4230/LIPIcs.ICALP.2023.5. <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2023.5> Abstract (the Skolem problem arises in loop termination).
- Positivity Problems for Low-Order Linear Recurrence Sequences — J. Ouaknine, J. Worrell, SODA 2014, arXiv:1307.2779, Sec. 1 (termination of linear programs as an application) and Sec. 2 (matrix form of an LRS and the Cayley–Hamilton converse). <https://arxiv.org/abs/1307.2779>
