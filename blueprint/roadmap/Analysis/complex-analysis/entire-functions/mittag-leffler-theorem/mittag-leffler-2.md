# Mittag-Leffler theorem for a sequence of poles with polynomial principal parts

Let $(b_\nu)_{\nu \in \mathbb{N}}$ be distinct complex numbers with $|b_\nu| \to \infty$ and let
$(P_\nu)$ be complex polynomials. Then:

1. there is a function $f : \mathbb{C} \to \mathbb{C}$, meromorphic on $\mathbb{C}$ and analytic off
   the set of the $b_\nu$, such that for every $\nu$ the function $f(z) - P_\nu\bigl((z - b_\nu)^{-1}\bigr)$
   agrees, on a punctured neighbourhood of $b_\nu$, with a function analytic at $b_\nu$;
2. there are polynomials $p_\nu$ such that the functions $f$ with these properties are exactly those
   for which there is an entire function $g$ with

    $$f(z) = g(z) + \sum_\nu \Bigl(P_\nu\bigl((z - b_\nu)^{-1}\bigr) - p_\nu(z)\Bigr)$$

    for every $z$ different from all $b_\nu$, the series converging.

A constant term of $P_\nu$ contributes nothing singular and is absorbed into $g$. Textbook statements usually normalize each $P_\nu$ to have zero constant term, so that $P_\nu\bigl((z - b_\nu)^{-1}\bigr)$ is a genuine singular part; that normalized form is the special case of the statement above. Unlike
[the Mittag-Leffler theorem](mittag-leffler.md) for a closed discrete set with finitely supported
coefficients, which asserts existence only, this form takes a sequence of poles with polynomial
principal parts and also describes all solutions.
