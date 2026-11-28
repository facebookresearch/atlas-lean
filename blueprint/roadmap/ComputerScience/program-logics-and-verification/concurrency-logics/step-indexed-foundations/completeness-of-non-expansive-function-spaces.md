# Completeness of non-expansive function spaces

The non-expansive functions from any OFE into a complete OFE form a complete OFE: limits are taken pointwise in the codomain, so the domain need not be complete.

**Lemma.** Let $T$ be an OFE and $U$ a COFE. Then $T \xrightarrow{ne} U$, with $f \overset{n}{=} g \iff \forall u.\ f(u) \overset{n}{=} g(u)$, is a COFE.

## Depends on

- [Non-expansive and contractive maps](non-expansive-and-contractive-maps.md)
- [Complete ordered families of equivalences](complete-ordered-families-of-equivalences.md)

## Proof depends on

- [Non-expansive and contractive maps](non-expansive-and-contractive-maps.md)
- [Complete ordered families of equivalences](complete-ordered-families-of-equivalences.md)

## Expansion

For a chain $(f_k)$ in $T \xrightarrow{ne} U$, each $(f_k(u))_k$ is a chain in $U$; let $g(u)$ be its limit. Then $g$ is non-expansive, since $u \overset{n}{=} u'$ gives $g(u) \overset{n}{=} f_n(u) \overset{n}{=} f_n(u') \overset{n}{=} g(u')$, and $f_n \overset{n}{=} g$ pointwise, so $g$ is a limit. The source uses this to note that only the uniform-predicate type and function spaces into it need to be complete.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 8.1 (the function space into a complete OFE is complete even if its domain is not, the limit being taken pointwise).
