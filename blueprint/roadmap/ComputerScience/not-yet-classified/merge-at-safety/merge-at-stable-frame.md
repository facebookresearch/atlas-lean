# Merge At Stable Frame

State fields which `merge_at` is forbidden to mutate.  The pending stack,
main data contents, temporary allocation, and adaptive `min_gallop` output are
intentionally absent because the operation may change them.
