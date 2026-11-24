# Merge At pending frame of eq some

Every defined `merge_at` result exposes the two source-selected adjacent
runs and retains the exact eager stack mutation, even when a later gallop or
merge reports failure. The remaining `PendingLayout` fields are framed across
the data movement.
