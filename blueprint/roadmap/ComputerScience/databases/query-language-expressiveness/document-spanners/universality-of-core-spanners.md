# Universality and equivalence of core spanners are not semi-decidable

Whether a core spanner representation defines the universal spanner, or whether two define the same spanner, is co-semi-decidable but not semi-decidable; whether one defines a regular spanner is neither.

**Theorem.** Over a fixed alphabet with at least two letters, for [core spanner representations](core-spanners.md):

1. universality ($[\![\rho]\!] = \Upsilon_{\mathsf{SVars}(\rho)}$?) and equivalence ($[\![\rho_1]\!] = [\![\rho_2]\!]$?) are not semi-decidable, but co-semi-decidable;
2. regularity (is $[\![\rho]\!]$ a regular spanner?) is neither semi-decidable nor co-semi-decidable.

All of this holds already for inputs from $\mathrm{RGX}^{\{\pi, \zeta^{=}, \cup\}}$.

## Depends on

- [Core spanners](core-spanners.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [Co-recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)

## Proof depends on

None.

## Expansion

Non-universality is semi-decided by enumerating words $w$ and comparing $[\![\rho]\!]\,(w)$, a computable finite set, with all tuples. For the lower bounds, Freydenberger showed for extended regular expressions (with backreferences) over an alphabet of at least two letters that $L(\alpha) = \Sigma^*$ is not semi-decidable and that regularity of $L(\alpha)$ is neither semi- nor co-semi-decidable; his expressions $\alpha_X$, built from a Turing machine $X$, use a single variable whose binding and references lie outside every Kleene star. Such variable-star-free expressions convert effectively into Boolean core spanner representations with the same language (the source's Theorem 3.21), and Boolean regular spanners recognize exactly the regular languages. The undecidability persists with a bounded number of spanner variables, and with equal-length selection in place of string equality.

## Sources

- Dominik D. Freydenberger and Mario Holldack, "Document spanners: from expressive power to decision problems", *Theory of Computing Systems* 62(4), 854–898, 2018, <https://doi.org/10.1007/s00224-017-9770-0>; read as the open-access publisher version, <https://link.springer.com/content/pdf/10.1007/s00224-017-9770-0.pdf>: Theorem 4.6 and its proof, using Theorem 3.21.
- Dominik D. Freydenberger, "Extended regular expressions: succinctness and decidability", *Theory of Computing Systems* 53(2), 159–193, 2013, <https://doi.org/10.1007/s00224-012-9389-0>: the undecidability results for extended regular expressions used in the proof, as recalled in the proof of Theorem 4.6 of the open-access copy above.
