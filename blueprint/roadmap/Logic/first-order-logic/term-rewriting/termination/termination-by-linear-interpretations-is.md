# Termination by linear interpretations is undecidable

It is undecidable whether a rewrite system consisting of a single rule can be proved terminating by a monotone linear interpretation over the natural numbers, and also whether a rewrite system can be proved terminating by a polynomial interpretation over the rationals or the reals.

**Theorem (Mitterwallner, Middeldorp and Thiemann).** A *linear interpretation over $\mathbb N$* assigns to each $k$-ary function symbol $f$ a function $f_{\mathbb N}(x_1, \ldots, x_k) = f_0 + f_1 x_1 + \cdots + f_k x_k$ with $f_0 \in \mathbb N$ and $f_1, \ldots, f_k \in \mathbb N_{\ge 1}$ (so that it is strictly monotone); it *proves termination* of a term rewrite system $R$ if $[\ell]_{\mathbb N} > [r]_{\mathbb N}$ for every rule $\ell \to r$ of $R$ and every assignment of natural numbers to the variables. Then:

1. it is undecidable whether a given one-rule term rewrite system can be proved terminating by a linear interpretation over $\mathbb N$ (Theorem 5 and Corollary 6 of the source);
2. this remains undecidable for one-rule systems that can be proved terminating by a (non-linear) polynomial interpretation over $\mathbb N$ (Corollary 8);
3. for $D \in \{\mathbb Q, \mathbb R\}$, it is undecidable whether a given term rewrite system can be proved terminating by a polynomial interpretation over $D$ (Theorem 12 and Corollary 13).

A *polynomial interpretation over $D$* assigns to each $k$-ary symbol a polynomial with coefficients in $D$ that maps $D_{\ge 0}^k$ to $D_{\ge 0}$; for a fixed $\delta \in D$ with $\delta > 0$, write $x >_\delta y$ if $x \ge y + \delta$. The interpretation proves termination of $R$ if each interpretation function is monotone for $>_\delta$ in every argument and $[\ell]_D >_\delta [r]_D$ for every rule $\ell \to r$ and every assignment of values in $D_{\ge 0}$ to the variables (Section 3 of the source, which takes the formal definitions from Neurauter and Middeldorp, 2014). The input in every part is a finite term rewrite system over a finite signature.

The refereed version proves part 3 for one-rule systems and shows by the same reduction that termination by the Knuth–Bendix order with subterm coefficients is undecidable. Undecidability of termination by polynomial interpretations over $\mathbb N$ was proved earlier by Mitterwallner and Middeldorp; general termination of finite rewrite systems is undecidable ([termination of term rewriting is undecidable](../termination-of-term-rewriting-is-undecidable.md)).

## Depends on

- [Term rewriting systems](../../automated-deduction/term-rewriting-systems.md)
- [Knuth–Bendix ordering](../knuth-bendix-ordering.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

By Hilbert's tenth problem it is undecidable, for polynomials $P, Q$ with positive integer coefficients, whether $P(x_1, \ldots, x_n) \ge Q(x_1, \ldots, x_n)$ for some $x_1, \ldots, x_n \in \mathbb N_{\ge 1}$ (Lemma 1): a polynomial equation $R = 0$ over $\mathbb Z$ is solvable iff $R(a_1x_1, \ldots, a_nx_n)^2 \le 0$ for some signs $a_i \in \{-1, 0, 1\}$ and positive $x_i$, and the square splits as a difference of polynomials with positive coefficients. A polynomial is encoded as a term built from a binary symbol $a$, unary symbols $v_1, \ldots, v_n$ and constants, and the single rule

$$
f(y_1, y_2, a(\ulcorner P\urcorner_{y_3}, y_3), o) \to f(a(y_1, z), a(z, y_2), a(\ulcorner Q\urcorner_{y_3}, y_3), z)
$$

forces every linear interpretation orienting it to interpret $a$ as addition, so that orienting the rule amounts to $P(v_1, \ldots, v_n) \ge Q(v_1, \ldots, v_n)$ for the positive coefficients $v_i$ of the interpretations of the $v_i$; conversely such values give an orienting interpretation (Theorem 5). Over $\mathbb Q$ and $\mathbb R$ an eight-rule system plays the same role (Theorem 12).

## Sources

- F. Mitterwallner, A. Middeldorp and R. Thiemann, "Linear Termination is Undecidable", in *Proceedings of the 39th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2024)*, ACM, 2024, pp. 1–12, <https://doi.org/10.1145/3661814.3662081>; read as arXiv:2307.14805v1 ("Linear Termination over N is Undecidable"), <https://arxiv.org/abs/2307.14805v1>: Lemma 1, Definition 4, Theorem 5, Corollaries 6 and 8, Theorem 12 and Corollary 13; the one-rule strengthening of part 3 and the Knuth–Bendix result are taken from the refereed version's abstract, read in the open-access copy at that address.
