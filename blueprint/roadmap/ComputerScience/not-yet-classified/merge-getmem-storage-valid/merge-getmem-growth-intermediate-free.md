# Merge Getmem growth intermediate free

`merge_freemem`'s preservation theorem supplies the representation fact
for the exact intermediate state used by the growth branch.  Liveness rules
out a fabricated already-released input, leaving precisely the inline-retain
and heap-release source cases.
