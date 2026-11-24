# Listsort merge Cost bound

The genuine CPython listsort model has exact logical merge-cost
accounting and satisfies the Munro--Wild PowerSort bound.

For every validated keyed or unkeyed input within `PY_LIST_MAX`, and for every
total Boolean comparator (with no order law), the real traced evaluator
successfully returns.  Its policy trace replays to an implementation merge
plan on the exact adaptive-run profile; its logical merge-event cost is that
plan's weighted external path length.  A source-faithful canonical PowerSort
plan on the same leaves dominates the actual CPython final-collapse schedule,
so the implementation cost is at most `nH + 2n`, and hence at most the optimal
alphabetic merge cost plus `2n`.

The returned certificate also exposes exact empty and singleton behavior.  On
inputs of length at least two it retains the execution-indexed reached state
at the real `merge_force_collapse` call, the historical open-forest invariant,
the exact CPython collapse-cost relation, and literal canonical-completion
identity.
