# Schwichtenberg's theorem

Let $\mathrm{int} = (\alpha \to \alpha) \to (\alpha \to \alpha)$ for a fixed type variable $\alpha$, and let $c_n = \lambda s.\, \lambda z.\, s^n z$ be the Church numerals, all of type
$\mathrm{int}$. A function $f : \mathbb{N}^m \to \mathbb{N}$ is *λ→-definable* if there is a pure term $F$ with $\vdash F : \mathrm{int} \to \cdots \to \mathrm{int} \to \mathrm{int}$ in
[simple type assignment](simple-type-assignment-a-la-curry.md) ($m + 1$ occurrences of $\mathrm{int}$) such that $F\, c_{n_1} \cdots c_{n_m} =_\beta c_{f(n_1, \dots, n_m)}$ for all
arguments.

**Theorem.** The λ→-definable functions are exactly the [extended polynomials](extended-polynomials.md).

Representing numbers by terms of different types, rather than uniformly by $\mathrm{int}$, makes more functions definable.

## Depends on

- [Beta equivalence in the untyped term model](../system-f/the-existing-untyped-beta-conversion-term-model/beta-eq.md)
- [Simple type assignment à la Curry](simple-type-assignment-a-la-curry.md)
- [Extended polynomials](extended-polynomials.md)

## Expansion

This page becomes ready once:

- H. Schwichtenberg, "Definierbare Funktionen im λ-Kalkül mit Typen", *Archiv für mathematische Logik und Grundlagenforschung* 17:113–114, 1976, as listed in the bibliography of the lecture notes below, to be checked for the hard direction (source check)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Definition 3.5.1 (λ→-definability), Lemmas 3.5.2–3.5.4 (projections, constants, signum, addition and multiplication are definable) and Theorem 3.5.6 (Schwichtenberg), whose hard direction the notes cite without proof.
- M. Zakrzewski, "Definable functions in the simply typed λ-calculus", arXiv:cs/0701022v1, 2007, <https://arxiv.org/abs/cs/0701022v1>: Section 1 (Schwichtenberg's characterization for numerals over a base type with β-conversion) and Section 1.1 (Definition 1 and the terms defining addition, multiplication and ifzero).
