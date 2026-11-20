# Applied domains

Use `Domains/<Subject>/` for a proved model whose definitions or hypotheses belong to a particular field. Pick the subject of the result, not the field that first needed it. A life table belongs in biology; a finite Markov-chain convergence theorem belongs in `MathlibExt`. Bioinformatics algorithms belong in `CSLibExt`, and physical models that extend Physlib belong in `PhyslibExt`.

- [Biology: demography](Biology/Demography/)
- [Economics: accounting](Economics/Accounting/)
- [Transport: accessibility](Transport/)
- [Urban planning: demand and stock balance](Urban/)

Add subjects here rather than adding a Lake library for each field. `Domains` may import `MathlibExt`, `CSLibExt`, and `PhyslibExt`. Those libraries must not import `Domains`. If two layers need a generic result, extract it into the appropriate foundation; put the domain-specific corollary here. Do not import `WantedExt` or tests. Tests mirror the production path in [`DomainsTest`](../DomainsTest/).

These subjects are moving incrementally. For biology not yet migrated, see the [existing models and modeling conventions](../MathlibExt/Biology/README.md). A module's import path changes when it moves, but its public declaration names can stay unchanged.
