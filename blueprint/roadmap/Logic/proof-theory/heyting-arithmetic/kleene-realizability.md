# Kleene realizability

For a number $e$ and a closed formula $\varphi$ of arithmetic, *$e$ realizes $\varphi$* is defined by induction on $\varphi$, writing $\{e\}$ for the partial recursive function
with Gödel number $e$ and $2^a 3^b$ for the coded pair:

1. $e$ realizes an atomic formula $A$ if $e = 0$ and $A$ is true;
2. $e$ realizes $\varphi_1 \wedge \varphi_2$ if $e = 2^a 3^b$ where $a$ realizes $\varphi_1$ and $b$ realizes $\varphi_2$;
3. $e$ realizes $\varphi_1 \vee \varphi_2$ if $e = 2^0 3^a$ with $a$ realizing $\varphi_1$, or $e = 2^1 3^a$ with $a$ realizing $\varphi_2$;
4. $e$ realizes $\varphi_1 \to \varphi_2$ if $\{e\}$ is a partial recursive function of one argument such that $\{e\}(a)$ is defined and realizes $\varphi_2$ whenever $a$ realizes $\varphi_1$;
5. $e$ realizes $\exists x\, \varphi(x)$ if $e = 2^n 3^a$ where $a$ realizes $\varphi(\underline{n})$;
6. $e$ realizes $\forall x\, \varphi(x)$ if $\{e\}$ is a total recursive function with $\{e\}(n)$ realizing $\varphi(\underline{n})$ for every $n$.

A closed formula is *realizable* if some number realizes it, and a formula with free variables $x_1, \dots, x_k$ is realizable if a total recursive $f$ gives a
realizer $f(n_1, \dots, n_k)$ of each instance. No number realizes $\bot$.

## Depends on

- [Heyting arithmetic](heyting-arithmetic.md)
- [Numerals](../../first-order-logic/peano-arithmetic-and-robinson-s-q/numeral.md)

## Expansion

This page becomes ready once:

- An acceptable numbering $e \mapsto \{e\}$ of the partial recursive functions, with a primitive recursive pairing (statement prerequisite; not yet stated)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Section 11.5, Definition 11.5.1 and the remarks after it.
