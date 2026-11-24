# Push Formed Run Traced

Push a run formed by the scan loop and retain the adaptive-minrun context
needed to interpret that leaf later.  The run and depth are derived rather
than accepted as metadata, preventing those two fields from disagreeing with
the actual state transition.
