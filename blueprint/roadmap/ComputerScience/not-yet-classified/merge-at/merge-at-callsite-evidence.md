# Merge At Callsite Evidence

Facts exported from the actual `merge_at` preparation path for a
subsequent `merge_getmem` call.  In particular, the guard-relevant state frame
is proved from the transcribed control flow, while the two trimming facts are
kept separately rather than replacing them with an assumed sum bound.
