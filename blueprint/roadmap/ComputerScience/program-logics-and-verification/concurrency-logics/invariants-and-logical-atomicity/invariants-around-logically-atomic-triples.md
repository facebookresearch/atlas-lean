# Invariants around logically atomic triples

In Iris 1.0, an invariant can be opened around any expression with a logically atomic specification, not only around physically atomic ones: its content joins the atomic pre- and postcondition and its name joins the shared mask.

**Theorem (rule LAINV).** In the Iris 1.0 logic, if $\langle x.\ \triangleright R \ast \alpha \rangle\ e\ \langle v.\ \triangleright R \ast \beta \rangle^{\mathcal{E}_M}_{\mathcal{E}}$ and $\iota \notin \mathcal{E}_M$, then

$$
\boxed{R}^{\iota} \vdash \langle x.\ \alpha \rangle\ e\ \langle v.\ \beta \rangle^{\mathcal{E}_M}_{\mathcal{E} \uplus \{\iota\}},
$$

where $\boxed{R}^{\iota}$ is the Iris 1.0 invariant assertion and $\uplus$ requires $\iota \notin \mathcal{E}$.

## Depends on

- [Logically atomic triples](logically-atomic-triples.md)

## Proof depends on

- [Logically atomic triples](logically-atomic-triples.md)

## Expansion

The source presents this rule among the derived rules of logically atomic triples and does not print its derivation, which is not reproduced here. Missing prerequisites, as for the definition: Iris 1.0 invariants, view shifts and Hoare triples. The rule is the logically atomic counterpart of opening an invariant around a physically atomic expression.

## Sources

- R. Jung, D. Swasey, F. Sieczkowski, K. Svendsen, A. Turon, L. Birkedal and D. Dreyer, "Iris: Monoids and invariants as an orthogonal basis for concurrent reasoning", *Proceedings of the 42nd ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL 2015)*, pp. 637-650, 2015, <https://doi.org/10.1145/2676726.2676980>; author copy of the published version <https://iris-project.org/pdfs/2015-popl-iris1-final.pdf>, Section 7.1 and Figure 14 (rule LAINV).
