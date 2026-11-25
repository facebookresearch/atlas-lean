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
results of the same branch are separate pages, each with its own source. The first is the general
form: let $T$ be a theory, not necessarily complete, in a countable language, such that $T$ has a
model, and let $\Phi_0, \Phi_1, \dots$ be countably many sets of formulas, each set in finitely many
free variables $\bar x$, none of which is principal over $T$, where $\Phi(\bar x)$ is principal over
$T$ when some formula $\psi(\bar x)$ such that $T \cup \{\exists \bar x\, \psi\}$ has a model satisfies
$T \models \forall \bar x\, (\psi \to \varphi)$ for every $\varphi$ in $\Phi$; then $T$ has a countable
model in which no tuple satisfies every formula of any $\Phi_n$. The others are: every countable atomic
model of a complete theory is prime; and every model of a countable language has an
$\omega$-saturated elementary extension, which need not be countable. Versions for uncountable
languages are separate statements.

## Sources

- W. Hodges and T. Scanlon, *First-order model theory*, Stanford Encyclopedia of Philosophy, substantive revision
  25 January 2024, §3.4 "The omitting types theorem". <https://plato.stanford.edu/entries/modeltheory-fo/>
