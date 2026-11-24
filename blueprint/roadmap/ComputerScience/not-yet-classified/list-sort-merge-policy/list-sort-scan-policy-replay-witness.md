# List Sort Scan Policy Replay Witness

A successful scan trace is split at the exact call boundary where
`list_sort_impl` enters `merge_force_collapse`.  `scanEvents` includes every
actual `found_new_run` merge and every rich formed-run observation; the
`collapseEvents` suffix is literally the traced final-collapse call.
