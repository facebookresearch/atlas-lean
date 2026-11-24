# Pending Run

One active pending run. `base` is an index into `MergeState.data`.
The newest run has no initialized power until `found_new_run` processes its
successor, which is represented by `none`.
