# Merge Memory Call Event

Raw observations spanning one directional merge call.

`sourceLeftLength` and `sourceRightLength` retain the two run lengths before
`merge_at` trimming; `na` and `nb` are the lengths actually passed to the
directional merge.  `intermediateFree` is an observation slot, not a claim:
the later safety layer must prove when it is `none`, when it is `some`, and
that any supplied snapshot is the state immediately after `merge_freemem`.
Likewise, this record does not assert that `request`, `outcome`, or any of the
snapshots agree with the modeled transition.
