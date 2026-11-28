# Exclusive camera

The *exclusive camera* $\mathrm{EX}(T)$ over an OFE $T$ is defined so that at most one element can be owned: its elements are $\mathrm{ex}(x)$ for $x \in T$ and an invalid element, and every composition is invalid.

$$
\mathrm{EX}(T) \triangleq \{ \mathrm{ex}(x) \mid x \in T \} \uplus \{ \mathsf{inv} \}, \qquad \mathcal{V}(a) \triangleq \{ n \mid a \neq \mathsf{inv} \},
$$

every composition equals $\mathsf{inv}$, $|\mathrm{ex}(x)| \triangleq \bot$ (no core) and $|\mathsf{inv}| \triangleq \mathsf{inv}$, and $\mathrm{ex}(x) \overset{n}{=} \mathrm{ex}(y) \iff x \overset{n}{=} y$, $\mathsf{inv} \overset{n}{=} \mathsf{inv}$. For a set $X$ with the discrete OFE this is the exclusive resource algebra $\mathrm{EX}(X)$, and $\mathrm{ex}(x) \rightsquigarrow \mathrm{ex}(y)$ for all $x, y$.

## Depends on

- [Ordered families of equivalences](../step-indexed-foundations/ordered-families-of-equivalences.md)
- [Cameras](cameras.md)
- [Frame-preserving updates in cameras](camera-frame-preserving-updates.md)
- [Resource algebras as discrete cameras](resource-algebras-as-discrete-cameras.md)

## Proof depends on

- [Frame-preserving updates in cameras](camera-frame-preserving-updates.md)

## Expansion

Since $\mathrm{ex}(x)$ composes validly with no frame, any update from it is frame preserving, which gives the exclusive update. The source writes the invalid element as a lightning symbol.

## Sources

- Iris Team, "The Iris 3.1 documentation", technical documentation (not peer reviewed) that the JFP article cites as its appendix (Iris Team, 2017), version of April 29, 2019, <https://plv.mpi-sws.org/iris/appendix-3.1.pdf>, Section 4.6 (exclusive camera Ex(T) over an OFE and EX-UPDATE), supplementary documentation.
- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 3.1 (the exclusive RA EX(X) and EX-UPDATE).
