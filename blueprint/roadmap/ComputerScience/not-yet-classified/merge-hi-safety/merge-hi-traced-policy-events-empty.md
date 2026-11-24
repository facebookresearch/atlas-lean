# Merge Hi Traced policy Events empty

A raw directional `merge_hi` emits no merge-policy event.  Its enclosing
`merge_at` invocation owns the unique logical merge event, recorded before
the trimming gallops.
