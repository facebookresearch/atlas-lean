# List Sort Scan Invariant

State carried at every call of the run-discovery scan.  The adaptive
minrun generator is required only while unscanned input remains: the clipped
last target is allowed to consume the suffix and enter final collapse without
manufacturing a nonexistent next active generator state.
