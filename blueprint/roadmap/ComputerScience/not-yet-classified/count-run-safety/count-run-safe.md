# Count Run safe

On a nonempty, signed-size-representable in-bounds suffix, `count_run`
succeeds for an arbitrary Boolean comparator, uses no exhausted helper path,
preserves the explicit values mode and backing extent, and returns a run length
inside `[1, nremaining]`.
