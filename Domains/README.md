# Applied domains

Use `Domains/<Subject>/` for a proved model whose definitions or hypotheses belong to a particular field. Pick the subject of the result, not the field that first needed it. A life table belongs in biology; a finite Markov-chain convergence theorem belongs in `MathlibExt`. Bioinformatics algorithms belong in `CSLibExt`, and physical models that extend Physlib belong in `PhyslibExt`.

- [Biology: models and conventions](Biology/README.md)
- [Economics, finance, and accounting](Economics/)
- [Materials science: composition conventions](MaterialsScience/)
- [Operations research: inventory and its applications](OperationsResearch/)
- [Chemistry: aqueous equilibria and isotope patterns](Chemistry/)
- [Transport: accessibility](Transport/)
- [Urban planning: demand and stock balance](Urban/)

Add subjects here rather than adding a Lake library for each field. `Domains` may import `MathlibExt`, `CSLibExt`, and `PhyslibExt`. Those libraries must not import `Domains`. If two layers need a generic result, extract it into the appropriate foundation; put the domain-specific corollary here. Deferred results over these models belong in `WantedExt`, which may import `Domains`; never import `WantedExt` or tests here. Tests mirror the production path in [`DomainsTest`](../DomainsTest/).

## Updating an open pull request

After rebasing onto the migration, keep edits and new files in the destination directory. For `Biology`, `Economics`, `OperationsResearch`, `Transport`, and `Urban`, replace the `MathlibExt/` prefix with `Domains/` and the `MathlibExtTest/` prefix with `DomainsTest/`. Update `import` and `public import` lines for the moved modules, including in files outside these directories. Do not bulk-rename declaration namespaces: the existing public names are unchanged. Build the changed modules and tests, then run `scripts/check.sh`.

Financial models previously under `MathlibExt/Probability/Finance` now live under `Domains/Economics/Finance`; general variance, stopping, and tail-sum results live in their probability subjects instead. The existing [finite-state asset-pricing theorem](../MathlibExt/Probability/Finance/FundamentalTheoremAssetPricing.lean) stays at its synchronized source path; it is not duplicated here. The materials composition model is in `Domains/MaterialsScience`, not the condensed-matter physics directory. If a foundation module needs a result from a moved file, keep the generic result in the foundation rather than adding an import from `Domains` or restoring the old file.
