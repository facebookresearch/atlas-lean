# List Sort Cleanup Memory Event

The raw merge-memory boundary emitted by the top-level cleanup.

The two snapshots are computed from the actual state passed to
`mergeFreemem`, rather than reconstructed from its released result.
