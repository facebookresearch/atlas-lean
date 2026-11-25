# Completeness of indexed interval search

Let $T$ be an indexed interval tree satisfying
its representation invariant, and let $Q$ be a valid query interval (low endpoint at most high
endpoint). If some entry stored in $T$ has an interval that overlaps $Q$ (each interval's low
endpoint is at most the other's high endpoint), then searching $T$ for $Q$ returns some entry.
