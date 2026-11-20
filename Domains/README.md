# Applied domains

Use `Domains/<Subject>/` for a proved model whose definitions or hypotheses belong to a particular field. Pick the subject of the result, not the field that first needed it. A life table belongs in biology; a finite Markov-chain convergence theorem belongs in `MathlibExt`. Bioinformatics algorithms belong in `CSLibExt`, and physical models that extend Physlib belong in `PhyslibExt`.

- [Biology: demography](Biology/Demography/)
- [Economics: accounting](Economics/Accounting/)
- [Transport: accessibility](Transport/)
- [Urban planning: demand and stock balance](Urban/)

Add subjects here rather than adding a Lake library for each field. `Domains` may import `MathlibExt`, `CSLibExt`, and `PhyslibExt`. Those libraries must not import `Domains`. If two layers need a generic result, extract it into the appropriate foundation; put the domain-specific corollary here. Do not import `WantedExt` or tests. Tests mirror the production path in [`DomainsTest`](../DomainsTest/).

These subjects are moving incrementally. For biology not yet migrated, see the [existing models and modeling conventions](../MathlibExt/Biology/README.md).

## Updating an open pull request

After rebasing onto the migration, keep edits and new files in the destination directory. For `Biology/Demography`, `Economics/Accounting`, `Transport`, and `Urban`, replace the `MathlibExt/` prefix with `Domains/` and the `MathlibExtTest/` prefix with `DomainsTest/`. Update `import` and `public import` lines for the moved modules, including in files outside these directories. Do not bulk-rename declaration namespaces: the existing public names are unchanged. Build the changed modules and tests, then run `scripts/check.sh`.

Other subjects need no path changes for this batch. If a foundation module needs a result from a moved file, keep the generic result in the foundation rather than adding an import from `Domains` or restoring the old file.
