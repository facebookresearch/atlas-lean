# Reverse Slice Phase Traced safe

Every source-valid physical `reverse_slice` terminates without exhausting
its distance fuel, preserves extent and values mode, and records only in-bounds
ordinary accesses.  A key phase is valid in either storage mode; a values phase
is valid only when synchronized-values storage is present.
