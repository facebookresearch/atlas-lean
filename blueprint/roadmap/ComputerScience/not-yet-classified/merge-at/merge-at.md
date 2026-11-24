# Merge At?

Transcription of CPython's `merge_at`.

`none` denotes an input outside the source assertion domain or a failed
modeled array access.  In particular, the function accepts exactly one of the
top two legal merge positions.  Once those checks pass, the stack is updated
before trimming, as in the source.
