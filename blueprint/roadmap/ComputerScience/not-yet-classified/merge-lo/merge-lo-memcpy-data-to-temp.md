# Merge Lo Memcpy Data To Temp?

Copy a main-list range into the distinct temporary store.  This recursive
bulk-copy implementation itself requires a pinned call-site tag and a proof of
its physical direction, so there is no untagged memcpy-capable helper for an
evaluator call to bypass.
