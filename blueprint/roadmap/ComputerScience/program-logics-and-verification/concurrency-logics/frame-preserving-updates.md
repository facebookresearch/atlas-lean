# Frame-preserving updates

In a [resource algebra](resource-algebras.md) $M$, an element $a$ has a *frame-preserving update* to a set $B \subseteq M$, written $a \rightsquigarrow B$, if

$$\forall c^? \in M^?.\ \mathcal{V}(a \cdot c^?) \Rightarrow \exists b \in B.\ \mathcal{V}(b \cdot c^?),$$

and $a \rightsquigarrow b$ abbreviates $a \rightsquigarrow \{b\}$. Thinking of the frame $c^?$ as the composition of the resources owned by all other threads, possibly none ($c^? = \bot$), a frame-preserving update never invalidates the resources of concurrently running threads. In Iris, ownership $[a]^\gamma$ of ghost state can be changed by a view shift along any frame-preserving update.

## Depends on

- [Resource algebras](resource-algebras.md)

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151>, Section 2.1, Figure 3 and the discussion of frame-preserving updates, and Figure 4 (rule GHOST-UPDATE).
