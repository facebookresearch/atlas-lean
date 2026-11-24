# Array Write?

Low-level array-write instrumenter shared by the region-specific wrappers.
Rejected writes leave the source array untouched by returning `none`, while
retaining the event.  Callers should not supply ad-hoc labels for listsort
storage.
