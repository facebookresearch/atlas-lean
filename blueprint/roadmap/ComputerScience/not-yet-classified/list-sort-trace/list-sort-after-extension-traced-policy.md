# List Sort After Extension Traced policy Events of success

On the successful post-extension path, the actual scan trace places the
formed-run observation after every policy event emitted by `found_new_run` and
before every event emitted by the recursive continuation.  The event retains
the natural-run length and adaptive-minrun target separately from the physical
run length that was pushed.
