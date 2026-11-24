# Push Pending Run restores powered Prefix

After the push, every former stack entry is in the initialized power
prefix and the new physical top is the unique entry whose stored power is not
constrained.  Exact boundary labels are transported directly from the virtual
post-push list in `ReadyToPush`.
