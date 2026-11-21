# AC-3 algorithm

- [Binary constraint satisfaction problem](binary-csp.md)
- [Solution of a binary CSP within given domains](is-solution.md)
- [Arc consistency](arc-consistent.md)
- [Symmetric binary CSP](symmetric.md)
- [Revision of an arc](revise.md)
- [In-degree of a variable](indeg.md)
- [Arcs requeued after a revision](requeue.md)
- [Termination potential of AC-3](potential.md)
- [A shrinking revision lowers the potential](potential-lt.md)
- [The AC-3 algorithm](ac3.md)
- [AC-3 on the whole problem](ac3-all.md)

## Soundness

- [AC-3 only shrinks domains](ac3-subset.md)
- [Revision keeps solution values](mem-revise-of-is-solution.md)
- [No solution is lost](is-solution-ac3.md)
- [Solutions survive AC-3](mem-ac3-of-is-solution.md)
- [An emptied domain rules out solutions](not-is-solution-of-ac3-eq-empty.md)

## Arc consistency of the result

- [Arc consistency after one AC-3 revision](arc-consistent-step.md)
- [Arc consistency invariant of AC-3](arc-consistent-ac3-of-inv.md)
- [AC-3 makes every arc consistent](arc-consistent-ac3.md)

## Termination bound

- [AC-3 revisions are bounded by the potential](ac3-time-le-potential.md)
- [Bound on the number of AC-3 revisions](ac3-time-le.md)
