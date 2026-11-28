# Later OFE

For an OFE $T$, the *later* OFE $\blacktriangleright T$ is defined as a copy of $T$ whose step-indexed equality is shifted up by one, making everything one level more equal than in $T$.

$$
\blacktriangleright T \triangleq \{ \mathrm{next}(x) \mid x \in T \}, \qquad \mathrm{next}(x) \overset{n}{=} \mathrm{next}(y) \iff n = 0 \lor x \overset{n-1}{=} y .
$$

$\blacktriangleright T$ is complete whenever $T$ is.

## Depends on

- [Ordered families of equivalences](ordered-families-of-equivalences.md)
- [Complete ordered families of equivalences](complete-ordered-families-of-equivalences.md)

## Proof depends on

- [Ordered families of equivalences](ordered-families-of-equivalences.md)
- [Complete ordered families of equivalences](complete-ordered-families-of-equivalences.md)

## Expansion

The relations are equivalences (total at index 0) that refine as $n$ grows, and equality at every index means equality in $T$, so $\blacktriangleright T$ is an OFE. If $T$ is complete, a chain $(\mathrm{next}(c_k))$ in $\blacktriangleright T$ gives the chain $(c_{k+1})$ in $T$, and $\mathrm{next}$ of its limit is a limit; so the later functor maps COFEs to COFEs. The later functor is the archetypical locally contractive bifunctor used to apply the America-Rutten theorem. In the Iris model the later OFE is the guard placed on recursive occurrences of the type of propositions, as in the camera $\mathrm{AG}(\blacktriangleright \mathit{iProp})$ of named propositions.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 4.2 and Figure 8 (later OFE; all OFEs discussed there, the later OFE included, are complete), Section 4.6 (the later functor is locally contractive) and Section 4.7 (guarding recursive occurrences).
