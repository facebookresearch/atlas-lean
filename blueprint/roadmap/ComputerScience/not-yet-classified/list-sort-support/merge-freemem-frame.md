# Merge Freemem frame

Final cleanup preserves every non-storage field, the stale capacity and
mode metadata, and the representation invariant. Liveness is deliberately not
claimed after a heap-backed cleanup.
