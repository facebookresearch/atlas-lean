# Chen-Liu-Vigoda: optimal mixing of Glauber dynamics in the uniqueness regime

For spin systems on graphs of maximum degree $\Delta = O(1)$ that are $\eta$-spectrally independent with $\eta = O(1)$ and have marginals bounded away from $0$ (for instance the hardcore model below the uniqueness threshold and antiferromagnetic two-spin systems in uniqueness), Glauber dynamics has optimal mixing time $O(n\log n)$ and satisfies approximate tensorization of entropy with a constant factor.

## Proof sketch

Upgrade spectral independence to entropic independence: show approximate tensorization of entropy for block dynamics with blocks of linear size via local-to-global arguments for entropy (rather than variance) on the partial-assignment complex. Bounded degree and bounded marginals then reduce block factorization to single-site factorization with constant loss, giving the modified log-Sobolev constant $\Omega(1/n)$.

## Depends on

- [Spectral independence of a distribution on the hypercube](../../../Combinatorics/polytopes-simplicial-complexes/local-spectral-high-dimensional-expanders/spectral-independence.md)

## Proof depends on

- [Spectral independence implies polynomial mixing of Glauber dynamics](../../../Combinatorics/polytopes-simplicial-complexes/local-spectral-high-dimensional-expanders/spectral-independence-glauber.md)

## Sources

- Zongchen Chen, Kuikui Liu, Eric Vigoda, "Optimal mixing of Glauber dynamics: entropy factorization via high-dimensional expansion", STOC (2021); arXiv:2011.02075.
