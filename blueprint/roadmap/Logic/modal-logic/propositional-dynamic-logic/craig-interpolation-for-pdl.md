# Craig interpolation for propositional dynamic logic

For a formula or program $\xi$ of propositional dynamic logic with tests, let its vocabulary be the
set of atomic formulas and atomic programs occurring in $\xi$. If $\varphi \to \psi$ is valid, in the
standard relational semantics, for PDL formulas $\varphi$ and $\psi$, then there is a PDL formula
$\theta$ whose vocabulary is contained in the vocabularies of both $\varphi$ and $\psi$ such that
$\varphi \to \theta$ and $\theta \to \psi$ are valid. This is the main theorem of Borzechowski,
Gattinger, Hansen, Ramanayake, Trucco Dalmas and Venema (preprint, 2025; version 3, 2026), whose proof builds on
Borzechowski's 1988 thesis; the authors record that the question had been open for many years and
that three earlier published proof attempts were criticized in the literature or retracted. Tests are
needed: for PDL without tests the corresponding statement fails (Gattinger, preprint, 2026).

## Depends on

- [PDL formulas](propositional-dynamic-logic-pdl/formula.md)
- [PDL programs](propositional-dynamic-logic-pdl/program.md)
- [Satisfaction of PDL formulas](propositional-dynamic-logic-pdl/sat.md)

## Expansion

A sound expansion defines the vocabulary of formulas and programs and validity, and follows the cited
proof: a cyclic tableau system for PDL with loaded formulas, its soundness and completeness, and the
construction of interpolants by pre-interpolants at tableau nodes and a quasi-tableau for clusters.
The failure of interpolation without tests is a separate page.

## Sources

- Manfred Borzechowski, Malvin Gattinger, Helle Hvid Hansen, Revantha Ramanayake, Francisco Trucco Dalmas and Yde Venema,
  "Propositional dynamic logic has Craig interpolation: a tableau-based proof", arXiv:2503.13276, version 3
  (2026), PDF numbering: Section 7.1, Definitions 7.1–7.2 and Theorem 7.3, with the proof overview in Section 7.2. <https://arxiv.org/pdf/2503.13276v3>
- M. Gattinger, "Propositional dynamic logic without tests does not have Craig interpolation",
  preprint (2026), abstract. <https://arxiv.org/abs/2611.16759>
