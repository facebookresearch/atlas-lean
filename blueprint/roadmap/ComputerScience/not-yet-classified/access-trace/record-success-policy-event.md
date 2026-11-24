# Record Success Policy Event

Append a policy event exactly when the modeled operation succeeds.

A failed operation retains its attempted lower-level accesses but does not
invent a completed logical transition.  Computing the event from the returned
value also permits future callers to retain result-dependent observations.
