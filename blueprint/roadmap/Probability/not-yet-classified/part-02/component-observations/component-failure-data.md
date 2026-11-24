# Component Failure Data

Single-cause infrastructure component failure data from an
observation table: `time (group i)` is component `i`'s exact
recorded event or censoring time; `failed i = true` means the
failure occurred at that time, and `failed i = false` means
right-censoring at that time. Components tied at the same
recorded time are counted together. Current-status inspection
data (failure known only to have occurred by inspection) is
not represented. No population consistency or identifiability
claim is made.
