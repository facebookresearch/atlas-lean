# Preserve unscanned update

Updating only an initial part of the unscanned suffix preserves correctness
of every already-pending run.  Structural fields and the pending array are
named explicitly, so the theorem cannot silently alter the represented prefix.
