# Frame-preserving updates in cameras

In a camera, an element is defined to have a *frame-preserving update* to a set when every frame compatible with it at some step index is also compatible, at that index, with some element of the set. This is the camera form of the resource-algebra notion.

For a camera $M$, $a \in M$ and $B \subseteq M$,

$$
a \rightsquigarrow B \iff \forall n,\ c^? \in M^?.\ n \in \mathcal{V}(a \cdot c^?) \Rightarrow \exists b \in B.\ n \in \mathcal{V}(b \cdot c^?),
$$

and $a \rightsquigarrow b$ abbreviates $a \rightsquigarrow \{b\}$. With full validity $\overline{\mathcal{V}}(a) \iff \forall n.\ n \in \mathcal{V}(a)$, a camera update is also an update in the resource-algebra sense.

## Depends on

- [Cameras](cameras.md)
- [Frame-preserving updates](../frame-preserving-updates.md)

## Proof depends on

- [Cameras](cameras.md)
- [Frame-preserving updates](../frame-preserving-updates.md)

## Expansion

The step index is quantified outside the frame, so the witness $b$ may depend on $n$. The implication to the resource-algebra notion is stated by the source; it uses that a frame valid at every index is in particular valid at each index.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 4.4 and Figure 9 (camera frame-preserving updates and the remark that they imply the resource-algebra version).
