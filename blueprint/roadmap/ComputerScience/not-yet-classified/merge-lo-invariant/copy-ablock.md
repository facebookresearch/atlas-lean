# Copy ABlock

Copying the upper-bound A prefix returned by `gallop_right` preserves the
semantic invariant.  The caller supplies the partition's comparison clause and
the strict survivor fact; the latter is derived from the high-end sentinel for
the actual gallop result.
