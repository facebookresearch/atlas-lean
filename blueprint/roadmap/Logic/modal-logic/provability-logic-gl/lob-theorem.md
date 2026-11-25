# Löb's theorem

In a Hilbert–Bernays–Löb provability structure with the diagonal property of the formalized Löb
theorem, if $T \vdash \mathrm{Prov}(A) \to A$ then $T \vdash A$. With $A = \bot$: if $T$ proves its
consistency statement $\neg\mathrm{Prov}(\bot)$, then $T \vdash \bot$ (Gödel's second
incompleteness theorem).

Proof: D1 gives $T \vdash \mathrm{Prov}(\mathrm{Prov}(A) \to A)$, the formalized Löb theorem gives
$T \vdash \mathrm{Prov}(A)$, and the hypothesis gives $T \vdash A$.

## Informally uses

- [Formalized Löb theorem](formalized-lob.md)

## Background

- [Gödel's second incompleteness theorem, abstract Hilbert–Bernays–Löb form](../../proof-theory/g-del-s-incompleteness-theorems/hilbert-bernays-lob-second-incompletenes.md): obtains the
  case $A = \bot$ from a Gödel sentence instead of the diagonal family used here.

## Sources

- M. H. Löb, "Solution of a problem of Leon Henkin", *Journal of Symbolic Logic* 20 (1955),
  115–118.
- R. Verbrugge, "Provability logic", *Stanford Encyclopedia of Philosophy*, substantive revision of 4 March 2024, §1 and §4.1.
