## Summary

<!-- Describe the mathematical or infrastructure change and its scope. -->

<!--
One `Graph:` line, as CONTRIBUTING.md asks: the article ids (`af_…`) of the
pages this pull request proves, fixes or extends, plus `new` when it adds
declarations that get pages (the next graph-sync batch writes them for a Lean
pull request), or `none` when it changes nothing the graph shows (`batch` on a
graph-sync batch). A new module may say where it goes on a `Place: <module> ->
<field>` line, outside this comment and before the merge; one in a folder that
is no subject needs one to get pages. Name each ready task it takes on a
`Tasks: af_…` line.
-->
Graph:

## Validation

- [ ] I ran `scripts/check.sh` from the repository root.

## MathlibExt

- [ ] New reusable mathematics is in `MathlibExt`, with tests or diagnostics in
      `MathlibExtTest`.
- [ ] Changed `MathlibExt` code contains no proof holes, custom axioms,
      `native_decide`, or imports from another project library.
- [ ] This pull request does not change `MathlibExt`, or the items above are
      complete.

## CSLibExt

- [ ] New reusable computer-science developments are in `CSLibExt`, with tests
      or diagnostics in `CSLibExtTest`.
- [ ] Changed `CSLibExt` code contains no proof holes, custom axioms,
      `native_decide`, or imports from `PhyslibExt`, `Domains`, `WantedExt`, or any test
      library.
- [ ] This pull request does not change `CSLibExt`, or the items above are
      complete.

## PhyslibExt

- [ ] New reusable physics developments extend upstream Physlib, with tests
      or diagnostics in `PhyslibExtTest`.
- [ ] Changed `PhyslibExt` code follows Physlib's conventions and contains no
      proof holes, custom axioms, `native_decide`, or imports from `Domains`, `WantedExt`
      or any test library.
- [ ] This pull request does not change `PhyslibExt`, or the items above are
      complete.

## Domains and DomainsTest

- [ ] Domain-specific models live in `Domains` and their tests in `DomainsTest`.
      The foundation libraries do not import these libraries.

## WantedExt

- [ ] Deferred results use direct `theorem_wanted` or `def_wanted`
      declarations and directly import `Batteries.Util.ProofWanted`.
- [ ] Changed `WantedExt` code contains no proof holes, custom axioms, or
      `native_decide`.
- [ ] This pull request does not change `WantedExt`, or the items above are
      complete.

## MathlibExtTest

- [ ] Changed tests and diagnostics contain no proof holes or custom axioms.
- [ ] This pull request does not change `MathlibExtTest`, or the item above is
      complete.

## CSLibExtTest

- [ ] Changed tests and diagnostics contain no proof holes or custom axioms.
- [ ] This pull request does not change `CSLibExtTest`, or the item above is
      complete.

## PhyslibExtTest

- [ ] Changed tests and diagnostics contain no proof holes or custom axioms.
- [ ] This pull request does not change `PhyslibExtTest`, or the item above is
      complete.
