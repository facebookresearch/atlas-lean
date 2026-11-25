# Full-sib recurrence in a finite pedigree

Let `pair t` name the two distinct individuals at generation $t$, up to generation $T$.
The generation-zero pair are founders, not necessarily siblings. Both individuals in each
subsequent generation have the preceding pair as parents. In the finite gene-dropping model,
all founder copies are distinct. For each $t \le T$, both individuals' within-individual
non-identity probabilities equal $h_t$, and their between-individual non-identity probability
equals $k_t$, where $(h_t,k_t)$ is the [full-sib recurrence](non-identity.md) started at $(1,1)$.
This calculation uses independent transmissions, not independent sibling ancestry.

## Sources

- J. Felsenstein, [*Theoretical Evolutionary Genetics*](https://felsenst.github.io/pgbook/pgbook.pdf),
  December 2019, §V.10, equations (V-26) and (V-27), pp. 234–235.
