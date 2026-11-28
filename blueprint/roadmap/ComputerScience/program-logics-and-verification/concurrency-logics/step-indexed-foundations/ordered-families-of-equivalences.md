# Ordered families of equivalences

An *ordered family of equivalences* (OFE) is a set equipped with one equivalence relation "equal for $n$ steps" for each step index $n$; the relations are defined to get finer as $n$ grows, and their intersection is equality.

An OFE is a pair $(T, (\overset{n}{=})_{n \in \mathbb{N}})$ of a set $T$ and relations $\overset{n}{=} \subseteq T \times T$ such that

- for every $n$, the relation $\overset{n}{=}$ is an equivalence relation;
- if $n \ge m$ and $x \overset{n}{=} y$, then $x \overset{m}{=} y$;
- $x = y$ exactly when $x \overset{n}{=} y$ for every $n \in \mathbb{N}$.

The *discrete* OFE on a set $X$ takes $x \overset{n}{=} y$ iff $x = y$, for every $n$.

## Depends on

- [Equivalence relation](../../../../Order/ordered-sets/equivalence-relation.md)

## Proof depends on

None.

## Expansion

The intuition in the source: $x \overset{n}{=} y$ means that no program running for at most $n$ steps can distinguish $x$ from $y$; the relations become finer as $n$ increases and agree with equality in the limit. The source attributes OFEs to Di Gianantonio and Miculan.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 4.2, Figure 7 (OFE-EQUIV, OFE-MONO, OFE-LIMIT) and Figure 8 (discrete OFE).
