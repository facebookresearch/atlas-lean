# Memmove From Traced mode safe

General two-store movement preserves the destination mode and leaves the
explicitly selected source store mode-valid.  For same-backing provenance the
source witness is the original destination invariant; for distinct provenance
it records that the separate source store is unchanged.
