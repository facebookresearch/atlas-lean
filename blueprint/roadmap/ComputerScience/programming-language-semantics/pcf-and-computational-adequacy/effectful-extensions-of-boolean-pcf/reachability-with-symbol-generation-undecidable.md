# Reachability for Boolean PCF with symbol generation is undecidable

Boolean PCF extended with a primitive that generates fresh symbols and an equality test on symbols has an undecidable reachability problem.

**Theorem.** Extend [Boolean PCF](boolean-pcf-and-its-reachability-problem.md) with a type $\mathbf{sym}$, an expression $\mathbf{gensym}()$ of type $\mathbf{sym}$ and, for $M_1, M_2 : \mathbf{sym}$, an equality test $M_1 = M_2 : \mathbf{bool}$, with reductions $E[\mathbf{gensym}()] \longrightarrow E[\ell]$ for a run-time label $\ell$ not occurring in $E$, $E[\ell = \ell] \longrightarrow E[\mathbf{true}]$ and $E[\ell_1 = \ell_2] \longrightarrow E[\mathbf{false}]$ for $\ell_1 \ne \ell_2$. The reachability problem for this language is undecidable.

## Depends on

- [Boolean PCF and its reachability problem](boolean-pcf-and-its-reachability-problem.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The encoding of a Minsky machine represents numbers by symbols. A symbol $\ell_{\mathit{zero}}$ represents $0$, and the program threads a decrement function $d$ through all program points. Incrementing $x$ generates a fresh symbol $y$ and returns it together with the updated decrement function $\lambda z.\ \mathbf{if}\ z = y\ \mathbf{then}\ x\ \mathbf{else}\ d(z)$. A zero test compares with $\ell_{\mathit{zero}}$, and a decrement applies $d$. A number other than $0$ may be represented by several symbols, which is harmless because the machine only tests for zero. Halting becomes $\mathbf{fail}$, so the machine halts iff the program reaches $\mathbf{fail}$.

## Sources

- Naoki Kobayashi, "On Decidable and Undecidable Extensions of Simply Typed Lambda Calculus", *Proceedings of the ACM on Programming Languages* 9(POPL), 2025, pp. 1136–1166, <https://doi.org/10.1145/3704875>; read as arXiv:2411.06086v2, <https://arxiv.org/abs/2411.06086v2>: the subsection "Extension with Symbol Generation" of the section "Undecidable Extensions of Boolean PCF", its theorem and encoding, of that version.
