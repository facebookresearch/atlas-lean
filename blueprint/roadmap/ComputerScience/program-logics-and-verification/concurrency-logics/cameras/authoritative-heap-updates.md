# Authoritative heap updates

For the authoritative camera over finite heaps, owning the authoritative heap together with a points-to fragment allows a store, and owning the authoritative heap alone allows allocation at a fresh location, each by a frame-preserving update.

Let $M = \mathrm{Loc} \xrightarrow{fin} \mathrm{EX}(\mathrm{Val})$. In $\mathrm{AUTH}(M)$, writing $[\ell \leftarrow v]$ for the singleton map to $\mathrm{ex}(v)$:

**Lemma.** For all heaps $\sigma$, locations $\ell$ and values $v, w$:

- $\bullet \sigma \cdot \circ [\ell \leftarrow v] \rightsquigarrow \bullet \sigma[\ell \leftarrow w] \cdot \circ [\ell \leftarrow w]$;
- if $\ell \notin \mathrm{dom}(\sigma)$, then $\bullet \sigma \rightsquigarrow \bullet \sigma[\ell \leftarrow w] \cdot \circ [\ell \leftarrow w]$.

## Depends on

- [Authoritative camera](authoritative-camera.md)
- [Finite partial function camera](finite-partial-function-camera.md)
- [Exclusive camera](exclusive-camera.md)
- [Frame-preserving updates in cameras](camera-frame-preserving-updates.md)

## Proof depends on

- [Authoritative camera](authoritative-camera.md)
- [Finite partial function camera](finite-partial-function-camera.md)
- [Exclusive camera](exclusive-camera.md)
- [Frame-preserving updates in cameras](camera-frame-preserving-updates.md)

## Expansion

The source states these updates as the ones needed for the store and allocation rules of weakest preconditions, and refers to its appendix for a generic mechanism deriving them. They follow because any frame compatible with the left-hand side has no authoritative part and its fragment avoids $\ell$ (in the first case because $\mathrm{ex}(v)$ admits no frame, in the second because $\ell$ is not allocated).

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 6.3.3 (the two frame-preserving updates for AUTH over the heap camera).
