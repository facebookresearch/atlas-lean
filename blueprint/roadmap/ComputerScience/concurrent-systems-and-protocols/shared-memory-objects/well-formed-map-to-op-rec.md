# Distinct completed operations yield well-formed records

Exporting a list of distinct completed operations from a single finite event history gives
an `OpRec` history with pairwise distinct event positions (`Linearizability.WellFormed`). This
holds for any payload encodings; pairing at consecutive occurrences of a process ensures that
no invocation or response position can be shared by two distinct operations. It does not
require the rest of the event history to be well formed.
