# Copy BBlock

Copying the strict B prefix returned by `gallop_left` preserves the
semantic invariant.  Unlike the A gallop, this block may exhaust B; the
resulting zero-right state is consumed by `succeed`.
