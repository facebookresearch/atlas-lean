# Finite partial function camera

For a countably infinite set $K$ and a camera $M$, the *finite partial function camera* $K \xrightarrow{fin} M$ is defined by lifting the camera structure of $M$ pointwise to finite partial maps; the empty map is its unit.

The elements are the finite partial functions $f : K \rightharpoonup M$. Two maps are $n$-equal if they have the same domain and $n$-equal values; composition is pointwise on the common domain and union elsewhere; the core is pointwise, keeping only the keys whose value has a core; $n \in \mathcal{V}(f)$ iff $n \in \mathcal{V}(f(k))$ for every $k$ in the domain. It has the updates: if $a \rightsquigarrow B$ then $f[i \leftarrow a] \rightsquigarrow \{ f[i \leftarrow b] \mid b \in B \}$ (JFP FMAP-UPDATE, documentation FPFN-UPDATE); if $a$ is valid (at every index) then $f \rightsquigarrow \{ f[i \leftarrow a] \mid i \notin \mathrm{dom}(f) \}$ (JFP FMAP-ALLOC); and, from the empty map, $\emptyset \rightsquigarrow \{ [i \leftarrow a] \mid i \in K \}$ for valid $a$ (documentation FPFN-ALLOC).

## Depends on

- [Cameras](cameras.md)
- [Frame-preserving updates in cameras](camera-frame-preserving-updates.md)

## Proof depends on

- [Cameras](cameras.md)
- [Frame-preserving updates in cameras](camera-frame-preserving-updates.md)

## Expansion

The allocation update is non-deterministic: the fresh key depends on the frame, and one exists because both maps are finite and $K$ is infinite. The source uses the camera $\prod_{i \in I} \mathbb{N} \xrightarrow{fin} M_i$ for the global ghost state and $\mathrm{Loc} \xrightarrow{fin} \mathrm{EX}(\mathrm{Val})$ for heaps.

## Sources

- Iris Team, "The Iris 3.1 documentation", technical documentation (not peer reviewed) that the JFP article cites as its appendix (Iris Team, 2017), version of April 29, 2019, <https://plv.mpi-sws.org/iris/appendix-3.1.pdf>, Section 4.4 (finite partial functions, pointwise lifting, FPFN-UPDATE and FPFN-ALLOC), supplementary documentation.
- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 3.2 (pointwise lifting through finite maps, FMAP-UPDATE and FMAP-ALLOC).
