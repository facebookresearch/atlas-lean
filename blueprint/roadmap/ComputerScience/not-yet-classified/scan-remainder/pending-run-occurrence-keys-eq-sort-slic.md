# Pending Run Occurrence Keys eq sort Slice Range Keys

The existing pending-run key view is definitionally the shared half-open
`SortSlice` key range.  This is the bridge used by local run and merge
correctness posts when they are assembled into `PendingRunsCorrect`.
