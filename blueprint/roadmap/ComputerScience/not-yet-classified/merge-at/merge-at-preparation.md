# Merge At Preparation

The observable continuation selected after `merge_at` has updated the
pending stack and completed both trimming gallops.  Keeping the two merge
continuations explicit makes the exact state and request at the subsequent
`merge_getmem` call available to assembly proofs.
