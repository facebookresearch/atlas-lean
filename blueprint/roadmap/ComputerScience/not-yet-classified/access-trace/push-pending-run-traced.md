# Push Pending Run Traced

Instrument the unconditional pending-run push.  The state update is the
same unbounded `Array.push` used by `list_sort_impl`; keeping this core wrapper
dependent only on `MergeState` lets every local transcribed evaluator import
the trace API without a dependency cycle.

This low-level compatibility wrapper records only the post-push depth because
it is not given run-discovery or adaptive-minrun metadata.  The real scan loop
must use `pushFormedRunTraced` below when it records a formed leaf.
