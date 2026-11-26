# Girard's definability theorem for System F

With the Church numerals $\underline{n} = \Lambda a.\, \lambda f{:}a \to a.\, \lambda x{:}a.\, f^n\, x$ of type $\mathrm{int} = \forall a.\, (a \to a) \to a \to a$, call a function
$f : \mathbb{N}^k \to \mathbb{N}$ *definable in System F* if a closed term $F : \mathrm{int} \to \cdots \to \mathrm{int} \to \mathrm{int}$ satisfies
$F\, \underline{m_1} \cdots \underline{m_k} =_\beta \underline{f(m_1, \dots, m_k)}$ for all arguments. The functions definable in System F are exactly the functions provably
total in second-order Peano arithmetic.

One direction formalizes the strong normalization proof of System F in second-order arithmetic; the other extends Gödel's Dialectica
interpretation to second-order arithmetic and System F.

## Depends on

- [Curry-style System F](curry-style-system-f.md)

## Proof depends on

- [Strong normalization of System F](../normalization-and-logical-relations/strong-normalization-of-system-f.md)
- [Gödel's Dialectica interpretation of Heyting arithmetic](../system-t/dialectica-interpretation-of-heyting-arithmetic.md)

## Expansion

This page becomes ready once:

- Second-order Peano arithmetic and its provably total recursive functions (statement prerequisite; not yet stated)
- A source with a complete proof, such as Girard's thesis, checked for the exact statement (source check)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Section 12.4 (data types in System F, including the integers) and Theorem 12.6.6 (Girard), with the paragraph before it.
