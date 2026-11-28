# Complete ordered families of equivalences

A *complete OFE* (COFE) is defined as an OFE in which every chain, a sequence whose elements become equal at ever higher indices, has a limit. Completeness is what fixed-point constructions over OFEs need.

Let $T$ be an OFE. A *chain* is a sequence $(c_n)_{n \in \mathbb{N}}$ in $T$ with $c_m \overset{n}{=} c_n$ whenever $n \le m$. A *limit* of the chain is an element $c_\infty \in T$ with $c_n \overset{n}{=} c_\infty$ for every $n$. $T$ is *complete*, a COFE, if every chain in $T$ has a limit. The category $\mathbf{COFE}$ has the COFEs as objects and the non-expansive functions as arrows.

## Depends on

- [Ordered families of equivalences](ordered-families-of-equivalences.md)
- [Non-expansive and contractive maps](non-expansive-and-contractive-maps.md)

## Proof depends on

- [Ordered families of equivalences](ordered-families-of-equivalences.md)

## Expansion

Limits are unique: two limits $c_\infty, d_\infty$ of one chain satisfy $c_\infty \overset{n}{=} c_n \overset{n}{=} d_\infty$ for every $n$, hence are equal by the limit axiom of OFEs. The source uses chains with limits to define objects as limits of approximations, and notes that all the OFEs it introduces before Section 4.3 are complete.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 4.2 and Figure 7 (OFE-COMPL, chains and limits) and Section 4.6 (the categories OFE and COFE).
