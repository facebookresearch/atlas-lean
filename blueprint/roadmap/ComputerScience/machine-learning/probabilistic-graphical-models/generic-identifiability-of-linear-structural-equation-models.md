# Complete efficient criteria for generic identifiability of linear structural equation models

This node records a research direction: for linear structural equation models given by a mixed graph, is there a complete graphical characterization of generic identifiability that can be decided efficiently?

## What would settle it

For an explicitly chosen family of mixed graphs, define a graphical criterion and prove that it is equivalent to generic injectivity of the parametrization (Λ, Ω) ↦ (I − Λ)^{−T} Ω (I − Λ)^{−1}, with the parameter domain and the exceptional set stated, together with a polynomial-time decision procedure.

## Status

No cited source poses this question in the form above; it is a research direction motivated by the cited results. This page does not certify the status or novelty of any particular formulation.

Foygel, Draisma and Drton give the half-trek criterion, a graphical condition sufficient for generic identifiability that can be checked in time polynomial in the size of the graph and does not require the directed part to be acyclic, together with a related necessary condition. Dörfler, van der Zander, Bläser and Liśkiewicz give a sound and complete algorithm for generic identification running in polynomial space, and prove that deciding whether a given feasible correlation matrix is explained by exactly one parameter set is hard for the complement of the existential theory of the reals, in particular coNP-hard.

This page records a research direction and asserts no theorem or present-status certification.

## Sources

- R. Foygel, J. Draisma and M. Drton, "Half-trek criterion for generic identifiability of linear structural equation models", Annals of Statistics 40 (2012), 1682–1713, abstract. <https://doi.org/10.1214/12-AOS1012>, preprint <https://arxiv.org/abs/1107.5552>
- J. Dörfler, B. van der Zander, M. Bläser and M. Liśkiewicz, "On the complexity of identification in linear structural causal models", preprint (2024), abstract. <https://arxiv.org/abs/2407.12528>
