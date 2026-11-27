# Containment of core spanners is not semi-decidable

No algorithm semi-decides whether one core spanner representation defines a spanner contained in another's, even for representations that use only regex formulas, projection and string-equality selection.

**Theorem.** Over a fixed alphabet with at least two letters, the containment problem for [core spanner representations](core-spanners.md) (given $\rho_1, \rho_2$, does $[\![\rho_1]\!]\,(w) \subseteq [\![\rho_2]\!]\,(w)$ hold for every word $w$?) is not semi-decidable, even when both inputs are restricted to $\mathrm{RGX}^{\{\pi, \zeta^{=}\}}$. It is co-semi-decidable.

## Depends on

- [Core spanners](core-spanners.md)

## Proof depends on

None.

## Expansion

The proof reduces the inclusion problem for pattern languages: given patterns $\alpha, \beta \in (\Sigma \cup X)^+$, is $L(\alpha) \subseteq L(\beta)$? It is undecidable for unbounded alphabets (Jiang, Salomaa, Salomaa and Yu) and for every fixed alphabet with at least two letters (Freydenberger and Reidenbach), also with boundedly many variables (Bremer and Freydenberger). A pattern converts into a representation $\rho_\alpha \in \mathrm{RGX}^{\{\zeta^{=}\}}$ with $L(\rho_\alpha) = L(\alpha)$; the Boolean spanners $\pi_\emptyset \rho_\alpha$ and $\pi_\emptyset \rho_\beta$ satisfy containment iff $L(\alpha) \subseteq L(\beta)$. With the bounded-variable result, the proof of Theorem 4.7 notes that containment stays not semi-decidable for $\mathrm{RGX}^{\{\pi, \zeta^{=}\}}$ representations with a bounded number of variables. Decidability of equivalence of pattern languages is open; undecidability there would make equivalence of $\mathrm{RGX}^{\{\pi, \zeta^{=}\}}$ representations undecidable.

## Sources

- Dominik D. Freydenberger and Mario Holldack, "Document spanners: from expressive power to decision problems", *Theory of Computing Systems* 62(4), 854–898, 2018, <https://doi.org/10.1007/s00224-017-9770-0>; read as the open-access publisher version, <https://link.springer.com/content/pdf/10.1007/s00224-017-9770-0.pdf>: Theorem 4.7 and its proof, using Theorem 3.3 (patterns as core spanners).
