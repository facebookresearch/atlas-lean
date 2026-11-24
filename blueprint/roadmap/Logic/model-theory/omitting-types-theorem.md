# Omitting types theorem

Let $L$ be a first-order language with countably many formulas, $T$ a complete theory in $L$, and
$\Phi$ a set of formulas of $L$ each having the free variable $x$ and no other free variable. A
structure realizes $\Phi$ when some element satisfies every formula in $\Phi$. A support of $\Phi$ in
$T$ is a formula $\psi(x)$ such that $T$ contains $\exists x\, \psi(x)$ and
$\forall x\, (\psi(x) \to \varphi(x))$ for every $\varphi$ in $\Phi$. If $\Phi$ has a support in $T$, then
every model of $T$ realizes $\Phi$. The omitting types theorem is the converse for countable models:
if every countable model of $T$ realizes $\Phi$, then $\Phi$ has a support in $T$. Equivalently, if
$\Phi$ has no support in $T$, then $T$ has a countable model in which no element satisfies every
formula of $\Phi$, that is, a countable model omitting $\Phi$.

The countability of the language is essential to this statement.

## Depends on

- [Complete theory of a first-order structure](../first-order-logic/theory-of-structure.md)

## Expansion

A sound expansion builds on first-order syntax and semantics, defines realizing and omitting
a set of formulas in one free variable and supports in a complete theory, which the statement uses,
and proves the theorem for countable languages (for example by a Henkin construction, as in the proof
of Gödel's completeness theorem, or a Baire-category argument). Further
results of the same branch are separate pages, each with its own source: prime and atomic models of
countable complete theories, and countable $\omega$-saturated elementary extensions. Versions for
several free variables and for uncountable languages are separate statements.

## Sources

- W. Hodges and T. Scanlon, *First-order model theory*, Stanford Encyclopedia of Philosophy, substantive revision
  25 January 2024, §3.4 "The omitting types theorem". <https://plato.stanford.edu/entries/modeltheory-fo/>
