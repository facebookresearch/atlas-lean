# Non-expansive and contractive maps

A map between OFEs is defined to be *non-expansive* when it preserves every step-indexed equality, and *contractive* when it turns equality below index $n$ into equality at index $n$; non-expansive maps form an OFE under the pointwise relations.

For OFEs $T$ and $U$, a function $f : T \to U$ is *non-expansive* if for all $n, x, y$,

$$
x \overset{n}{=} y \Rightarrow f(x) \overset{n}{=} f(y),
$$

and *contractive* if for all $n, x, y$,

$$
(\forall m < n.\ x \overset{m}{=} y) \Rightarrow f(x) \overset{n}{=} f(y).
$$

Contractiveness is equivalent to: $f(x) \overset{0}{=} f(y)$ for all $x, y$, and $x \overset{n}{=} y$ gives $f(x) \overset{n+1}{=} f(y)$. The set $T \xrightarrow{ne} U$ of non-expansive functions is an OFE with $f \overset{n}{=} g \iff \forall u.\ f(u) \overset{n}{=} g(u)$.

## Depends on

- [Ordered families of equivalences](ordered-families-of-equivalences.md)

## Proof depends on

- [Ordered families of equivalences](ordered-families-of-equivalences.md)

## Expansion

For $n = 0$ the premise of contractiveness is vacuous, and for $n + 1$ the premise $\forall m \le n.\ x \overset{m}{=} y$ is equivalent to $x \overset{n}{=} y$ by monotonicity of the relations; this is the equivalence the source states after Figure 7. In particular every contractive function is non-expansive. The pointwise relations on $T \xrightarrow{ne} U$ inherit the OFE axioms from $U$.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 4.2 and Figure 7 (OFE-NONEXP, OFE-CONTR and the equivalent form of contractiveness), Section 4.6 (the OFE structure on non-expansive functions).
