# List Sort Scan Reached Collapse

`openState` is the actual state at a successful terminal scan call, hence
the state passed by that call to `mergeForceCollapseTraced?`.

`bindPrefix` preserves this provenance through a genuine successful helper
prefix.  In particular, it cannot transport the certificate merely because
two executions happen to have equal policy-event projections.
