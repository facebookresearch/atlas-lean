# Arithmetization of syntax and the diagonal lemma

This node covers the coding of a formal language in arithmetic and its use in the incompleteness
theorems for formal systems $F$ containing Robinson arithmetic $\mathsf{Q}$. A set $S$ of natural
numbers is strongly representable in $F$ when some formula $A(x)$ with one free variable satisfies
$F \vdash A(\overline{n})$ for every $n \in S$ and $F \vdash \neg A(\overline{n})$ for every
$n \notin S$, where $\overline{n}$ is the numeral of $n$. An arithmetization (Gödel numbering) is an
effective correspondence between the expressions of the language and natural numbers, written
$\ulcorner E \urcorner$ for the code of $E$. The diagonalization lemma: for every formula $A(x)$ of
the language of $F$ with only one free variable, a sentence $D$ can be constructed mechanically such
that $F \vdash D \leftrightarrow A(\ulcorner D \urcorner)$.

## Expansion

A sound expansion fixes the language of arithmetic, the axioms of $\mathsf{Q}$, one coding of terms,
formulas and derivations, and a substitution function, and has separate pages for: strong and weak
representability; representability in $\mathsf{Q}$ of the computable relations needed (substitution,
the proof relation of a recursively axiomatized $F$); the diagonalization lemma; and the
instantiation of abstract incompleteness schemas through this coding. Hypotheses stated for $\mathsf{Q}$
must not be replaced by stronger ones (for example a theory with $\Sigma_1$ induction) without a
separate statement.

## Background

- [Gödel's incompleteness theorems](g-del-s-incompleteness-theorems/README.md): the abstract forms of
  the theorems that this coding instantiates.

## Sources

- P. Raatikainen, *Gödel's incompleteness theorems*, Stanford Encyclopedia of Philosophy, substantive
  revision 8 October 2025, §2.1–§2.4. <https://plato.stanford.edu/entries/goedel-incompleteness/>
