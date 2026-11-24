# Hilbert–Bernays–Löb provability structure

An abstract theory $T$ over a set of sentences with an implication $\to$ and a falsity $\bot$ (with
$\neg A = A \to \bot$): its theorems are closed under modus ponens and contain the axioms
$A \to (B \to A)$, $(A \to (B \to C)) \to ((A \to B) \to (A \to C))$ and $\neg\neg A \to A$, and it has
a provability operator $\mathrm{Prov}$ on sentences satisfying the derivability conditions

- D1: if $T \vdash A$ then $T \vdash \mathrm{Prov}(A)$;
- D2: $T \vdash \mathrm{Prov}(A \to B) \to (\mathrm{Prov}(A) \to \mathrm{Prov}(B))$;
- D3: $T \vdash \mathrm{Prov}(A) \to \mathrm{Prov}(\mathrm{Prov}(A))$.

Peano arithmetic with its standard provability predicate is the intended instance; here the
conditions are assumptions rather than consequences of an arithmetization. The hypotheses are
jointly satisfiable together with the diagonal property used below, without $\bot$ being a
theorem: take true propositions as theorems and a provability operator that holds of every
sentence, as in a theory proving its own inconsistency such as
$\mathrm{PA} + \neg\mathrm{Con}(\mathrm{PA})$.

## Background

- [Gödel's second incompleteness theorem, abstract Hilbert–Bernays–Löb form](../../proof-theory/g-del-s-incompleteness-theorems/hilbert-bernays-lob-second-incompletenes.md): the same
  derivability conditions, stated as separate hypotheses.

## Sources

- M. H. Löb, "Solution of a problem of Leon Henkin", *Journal of Symbolic Logic* 20 (1955),
  115–118.
- R. Verbrugge, "Provability logic", *Stanford Encyclopedia of Philosophy*, substantive revision of 4 March 2024, §1.
