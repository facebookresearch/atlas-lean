# Call-by-value and call-by-name agree on simply typed terms

Let $t$ be a closed well-typed term of the simply typed lambda calculus. Every reduction sequence from $t$ is finite, so call-by-value
evaluation of $t$ ends in a value $v$ and call-by-name evaluation (leftmost reduction to weak head normal form) ends in a weak head normal
form $w$. Both $v$ and $w$ are $\beta$-reducts of $t$, so by the Church–Rosser property they reduce to the unique $\beta$-normal form of $t$, and
$v =_\beta w$.

The agreement depends on termination. In PCF, let $\Omega$ be a closed divergent term of type $\mathrm{nat}$ such as $\mathrm{fix}\, x.\, x$. Then
$(\lambda x.\, 0)\, \Omega$ evaluates to $0$ under call by name, which substitutes the unevaluated argument, but diverges under call by value,
which first evaluates the argument.

## Depends on

- [Determinism of PCF call-by-name reduction](../pcf-and-computational-adequacy/deterministic-2.md)

## Proof depends on

- [Termination of the call-by-value simply typed lambda calculus](../../type-systems-and-lambda-calculi/normalization-of-the-simply-typed-lambda-calculu/terminates-closed.md)

## Expansion

This page becomes ready once:

- The Church–Rosser property of $\beta$-reduction for simply typed terms (statement prerequisite; not yet stated)
- Strong normalization of full $\beta$-reduction for simply typed terms (statement prerequisite; formal statement exists, page pending)

## Sources

- J.-Y. Girard, Y. Lafont and P. Taylor, *Proofs and Types*, Cambridge University Press, 1989: Section 4.4 and Chapter 6 (strong normalization of the simply typed lambda calculus) and Section 4.1 (Church–Rosser property and uniqueness of normal forms). The agreement statement is derived on this page from these two results.
- G. D. Plotkin, "Call-by-name, call-by-value and the λ-calculus", *Theoretical Computer Science* 1(2):125–159, 1975, <https://homepages.inf.ed.ac.uk/gdp/publications/cbn_cbv_lambda.pdf>: Section 1 (the two calling mechanisms and terms on which they differ).
