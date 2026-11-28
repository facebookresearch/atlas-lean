# Substructural sequent calculi beyond classical linear logic

This node covers sequent calculi that restrict Gentzen's structural rules (weakening, contraction
and exchange) other than full classical linear logic, whose cut elimination is a separate topic
([cut elimination for classical linear logic](cut-elimination-for-classical-linear-logic/README.md)),
together with phase semantics. Affine logic does not accept contraction; relevant logics reject
weakening; in the Lambek calculus neither contraction nor exchange is available, so the number and
the order of premises matter. Girard's phase semantics interprets a
formula of linear logic by a set of contexts with closure properties and gives a semantics of
provability for linear logic.

## Expansion

A sound expansion fixes, for each calculus separately, its formulas, the form of its contexts (lists or
multisets) and its rules, and has separate pages for: cut elimination for the Lambek calculus; cut
elimination for affine linear logic; phase spaces and the soundness and completeness for phase semantics of multiplicative-additive linear
logic and, separately, of full linear logic with exponentials, as stated in a source fixed for that
page; cut elimination for intuitionistic linear logic; and any decidability or complexity result, each
with its own source, reusing the undecidability pages for Lambek-style and relevant calculi in
[undecidable substructural calculi](undecidable-substructural-calculi/README.md) rather than restating them. The logic of bunched implications is outside this node and needs its own sources. Results for classical linear logic do not transfer
to these calculi without proof.

## Sources

- R. Di Cosmo and D. Miller, *Linear logic*, Stanford Encyclopedia of Philosophy, substantive revision
  16 September 2023, §1.1, §3.1 and §6.2. <https://plato.stanford.edu/entries/logic-linear/>
- G. Restall, *Substructural logics*, Stanford Encyclopedia of Philosophy, substantive revision
  15 August 2024, §2. <https://plato.stanford.edu/entries/logic-substructural/>
