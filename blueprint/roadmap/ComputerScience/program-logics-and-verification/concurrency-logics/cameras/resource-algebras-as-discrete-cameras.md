# Resource algebras as discrete cameras

Every resource algebra is a camera, called discrete: give it the discrete OFE and make each element valid at all step indices or at none, according to its validity. Users who need no higher-order ghost state can work with resource algebras alone.

**Lemma.** Let $(M, \mathcal{V}_{RA}, |\cdot|, \cdot)$ be a resource algebra. With the discrete OFE on $M$ and $\mathcal{V}(a) \triangleq \{ n \mid \mathcal{V}_{RA}(a) \}$, the tuple $(M, \mathcal{V}, |\cdot|, \cdot)$ is a camera, and every function between discrete OFEs is non-expansive.

## Depends on

- [Resource algebras](../resource-algebras.md)
- [Cameras](cameras.md)
- [Ordered families of equivalences](../step-indexed-foundations/ordered-families-of-equivalences.md)

## Proof depends on

- [Resource algebras](../resource-algebras.md)
- [Cameras](cameras.md)
- [Ordered families of equivalences](../step-indexed-foundations/ordered-families-of-equivalences.md)
- [Non-expansive and contractive maps](../step-indexed-foundations/non-expansive-and-contractive-maps.md)

## Expansion

On a discrete OFE every function is non-expansive, the extension axiom holds with $c_i = b_i$ because $n$-equality is equality, and validity is either every index or none, so the camera axioms reduce to the resource-algebra axioms.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 4.4 (every RA can be trivially turned into a camera with the discrete OFE; functions between discrete OFEs are non-expansive).
