# Step-indexed propositions

The OFE $\mathrm{SProp}$ of *step-indexed propositions* is defined as the set of downward-closed sets of natural numbers: a proposition is the set of step indices at which it is true, so it is true for no steps, for the first $k$ steps, or forever.

$$
\mathrm{SProp} \triangleq \{ X \subseteq \mathbb{N} \mid \forall n \ge m.\ n \in X \Rightarrow m \in X \},
$$

with $X \overset{n}{=} Y \iff \forall m \le n.\ (m \in X \Leftrightarrow m \in Y)$, and step-indexed inclusion $X \overset{n}{\subseteq} Y \iff \forall m \le n.\ (m \in X \Rightarrow m \in Y)$. The proposition $\mathbb{N}$ is true and $\emptyset$ is false; the elements of $\mathrm{SProp}$ correspond to the ordinals up to and including $\omega$. For every OFE $T$ and $x, y \in T$ the set $\{ n \mid x \overset{n}{=} y \}$ belongs to $\mathrm{SProp}$, and a non-expansive $f$ gives $\{ n \mid x \overset{n}{=} y \} \subseteq \{ n \mid f(x) \overset{n}{=} f(y) \}$. $\mathrm{SProp}$ is complete.

## Depends on

- [Ordered families of equivalences](ordered-families-of-equivalences.md)
- [Non-expansive and contractive maps](non-expansive-and-contractive-maps.md)
- [Complete ordered families of equivalences](complete-ordered-families-of-equivalences.md)

## Proof depends on

- [Ordered families of equivalences](ordered-families-of-equivalences.md)
- [Non-expansive and contractive maps](non-expansive-and-contractive-maps.md)
- [Complete ordered families of equivalences](complete-ordered-families-of-equivalences.md)

## Expansion

The set of indices at which $x \overset{n}{=} y$ is downward closed by monotonicity of the relations, and non-expansiveness gives the inclusion. A chain $(X_k)$ has the limit $\{ n \mid n \in X_n \}$: if $n \in X_n$ and $m \le n$, then $m \in X_n$ and $X_n \overset{m}{=} X_m$, so $m \in X_m$; and $X_k \overset{k}{=}$ the limit by the same comparison.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 4.1 (translation table), Section 4.2 and Figure 8 (SProp, its step-indexed equality and inclusion, index sets of equalities, and the remark that the OFEs discussed are complete).
