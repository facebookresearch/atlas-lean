# Higher-order agreement camera

The *higher-order agreement camera* $\mathrm{AG}(T)$ over an OFE $T$ is defined so that several owners can agree on one value, with agreement checked only up to the current step index; its elements are finite non-empty sets of values, composed by union.

$$
\mathrm{AG}(T) \triangleq \{ a \in \wp^{fin}(T) \mid a \neq \emptyset \}, \qquad a \cdot b \triangleq a \cup b, \qquad |a| \triangleq a, \qquad \mathrm{ag}(x) \triangleq \{x\},
$$

$$
a \overset{n}{=} b \iff (\forall x \in a.\ \exists y \in b.\ x \overset{n}{=} y) \land (\forall y \in b.\ \exists x \in a.\ x \overset{n}{=} y), \qquad \mathcal{V}(a) \triangleq \{ n \mid \forall x, y \in a.\ x \overset{n}{=} y \}.
$$

With these operations $\mathrm{AG}(T)$ is a camera, composition and $\mathrm{ag}$ are non-expansive, and for all $a, x, y, n$: $|a| \overset{n}{=} a$; $n \in \mathcal{V}(\mathrm{ag}(x))$; $n \in \mathcal{V}(\mathrm{ag}(x) \cdot \mathrm{ag}(y))$ gives $x \overset{n}{=} y$; $a \cdot a = a$ and $\mathrm{ag}$ is injective. If $T$ is discrete then so is $\mathrm{AG}(T)$. For an OFE $T$ and $x, y \in T$, validity of $\mathrm{ag}(\mathrm{next}(x)) \cdot \mathrm{ag}(\mathrm{next}(y))$ in $\mathrm{AG}(\blacktriangleright T)$ at an index $n > 0$ gives only $x \overset{n-1}{=} y$.

## Depends on

- [Cameras](cameras.md)
- [Ordered families of equivalences](../step-indexed-foundations/ordered-families-of-equivalences.md)
- [Non-expansive and contractive maps](../step-indexed-foundations/non-expansive-and-contractive-maps.md)
- [Step-indexed propositions](../step-indexed-foundations/step-indexed-propositions.md)
- [Later OFE](../step-indexed-foundations/later-ofe.md)

## Proof depends on

- [Cameras](cameras.md)
- [Ordered families of equivalences](../step-indexed-foundations/ordered-families-of-equivalences.md)
- [Later OFE](../step-indexed-foundations/later-ofe.md)

## Expansion

Union is associative, commutative and idempotent; validity is downward closed and decreases under composition. Non-expansiveness of union depends on the "each element has an $n$-equal partner" form of $\overset{n}{=}$; the source notes that the all-pairs relation would break it. Iris uses the last property with $T = \mathit{iProp}$, for named propositions. The construction replaces the first-order agreement algebra, whose composition tests exact equality and so is not non-expansive.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 4.3 (AG(T), AG-CORE-STEP, AG-VALID-STEP, AG-AGREE-STEP), Section 4.7 (SPROP-AGREE), Section 3.1 (AG0) and Section 8.1 (discreteness).
