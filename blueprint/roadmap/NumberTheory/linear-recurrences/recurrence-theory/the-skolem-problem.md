# The Skolem problem

An integer linear recurrence sequence of order $k \ge 1$ is a sequence $(u_n)_{n \ge 0}$ of integers satisfying
$u_{n+k} = a_{k-1}u_{n+k-1} + \cdots + a_0 u_n$ for all $n$, with fixed integers $a_0, \dots, a_{k-1}$.
The *Skolem problem* asks, given the coefficients and the initial values $u_0, \dots, u_{k-1}$, whether
$u_n = 0$ for some $n$.

**Question posed by the cited sources.** Is the Skolem problem decidable?

By the Skolem–Mahler–Lech theorem the zero set of such a sequence is the union of a finite set and finitely
many arithmetic progressions; known proofs of the theorem are not effective.

The problem is decidable if and only if there is a
computable function $B$ of the input such that whenever the sequence has a zero, it has one at an index
$n \le B$.

**Status (as of the sources below).** The problem is decidable for recurrences of order at most $4$
(Mignotte, Shorey and Tijdeman 1984; Vereshchagin 1985) and open already for order $5$. Bilu et al. (2022)
give an algorithm for simple recurrences whose termination relies on two classical conjectures about the
exponential function; Luca, Ouaknine and Worrell study large zeros and conditional decidability. These are
conditional results, not a resolution.

## Expansion

A good expansion separates:

1. Integer recurrences of positive order, their finite coefficient/initial-value encodings, computation of
    individual terms, and the predicate that some term is zero.
2. The qualitative Skolem–Mahler–Lech zero-set theorem from an effective finite search bound, including the
    stated equivalence between decidability and a computable bound on a first zero.
3. The cited low-order decidability results and the conditional results for their particular classes of
    recurrences, with simple/non-degenerate hypotheses and number-theoretic conjectures explicit rather
    than transferred to arbitrary recurrences.
4. The general decision question as a research node. A proposed positive solution needs a terminating,
    correct decision procedure on the full stated class; a conditional procedure does not settle it.

This page records the cited state of the question, not a certification of its present status.

## Sources

- J. Worrell, *The Skolem landscape*, invited talk, ICALP 2023, LIPIcs 261, 5:1–5:2, abstract. <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2023.5>
- F. Luca, J. Ouaknine and J. Worrell, *Conjectural decidability of the Skolem problem*, arXiv:2607.15510, abstract. <https://arxiv.org/abs/2607.15510>
