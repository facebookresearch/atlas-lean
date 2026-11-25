# Lazy sampling and the PRP/PRF switching lemma

## PMF helpers

- [Composition depends only on the support](bind-congr-support.md)
- [Images depend only on the support](map-congr-support.md)
- [Uniform distribution on a subset](cond-uniform.md)
- [Splitting a uniform distribution along a coordinate](cond-uniform-split.md)
- [Winning probability after a uniform choice](win-prob-bind-uniform-of-finset.md)

## Stateful oracles and lazy tables

- [Table of answers](table.md)
- [Empty table](empty.md)
- [Functions consistent with a table](consistent.md)
- [Extending a table](extends.md)
- [Running against a stateful randomized oracle](run-state.md)
- [Stateless oracles as stateful oracles](run-state-stateless-map-fst.md)
- [Lazy sampling step](lazy-step.md)
- [Recorded queries get their recorded answers](lazy-step-of-some.md)
- [Fresh queries are sampled and recorded](lazy-step-of-none.md)
- [Distribution of a fresh answer](lazy-step-map-fst-of-none.md)
- [Lazy runs never change recorded answers](extends-of-mem-support-run-state.md)
- [Table invariants preserved by lazy runs](inv-of-mem-support-run-state.md)

## Lazy = eager, generically

- [Consistent members of a family of functions](consistent-set.md)
- [Consistent functions with a prescribed fresh answer](filter-consistent-set.md)
- [Lazy sampling equals eager sampling](run-state-lazy-step-map-fst.md)

## The lazy random function

- [Lazy random function step](rf-step.md)
- [Lazy random function](lazy-rf.md)
- [Fresh answers of the lazy random function are uniform](rf-step-map-fst-of-none.md)
- [The lazy random function repeats recorded answers](rf-step-of-some.md)
- [Lazy random functions are random functions](lazy-rf-map-fst.md)

## The lazy random permutation

- [Unused values of a table](fresh-set.md)
- [Recording an answer uses up its value](fresh-set-update.md)
- [Lazy random permutation step](rp-step.md)
- [Lazy random permutation](lazy-rp.md)
- [Fresh answers of the lazy random permutation are uniform](rp-step-map-fst-of-none.md)
- [The lazy random permutation repeats recorded answers](rp-step-of-some.md)
- [Fresh answers of the lazy random permutation are unused values](rp-step-fst-mem-fresh-set.md)
- [Permutations as functions](perm-ev.md)
- [Tables that come from a permutation](perm-table.md)
- [Lazy random permutations are random permutations](lazy-rp-map-fst.md)
- [Lazy permutation tables keep coming from permutations](perm-table-of-mem-support-lazy-rp.md)
- [Distinct queries get distinct answers](injective-of-mem-support-lazy-rp.md)

## The switching lemma

- [Switching bound](switch-bound.md)
- [Lazy switching lemma](lazy-switching.md)
- [The PRP/PRF switching lemma](switching-lemma.md)
- [Switching lemma with the birthday bound](switching-lemma-le.md)
