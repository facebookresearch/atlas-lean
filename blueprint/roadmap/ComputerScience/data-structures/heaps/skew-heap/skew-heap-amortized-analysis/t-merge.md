# T merge

`T_merge`: the recursive-equation count of `merge` (Appendix B.10).
It counts one per recursive equation of `merge` — one per call,
including the leaf cases — following the same recursive branches as
`merge` itself. It is a count of recursive equations, not wall-clock
runtime, and not the cost of reusing a persistent state.
