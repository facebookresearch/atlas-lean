# Finish List Sort Traced?

Traced common `succeed`/`fail` cleanup.  The final reversal is one physical
`reverse_slice` call, selected from the retained storage-mode bit.  Every
successful cleanup appends one raw merge-memory boundary after the physical
reverse trace and before returning the post-cleanup state.
