# Record Success Memory Event

Append a boundary observation exactly when the modeled operation
succeeds.  A failed operation retains its existing trace and does not invent
a completed transition.  The event is computed from the actual successful
result, rather than from a separately supplied witness.
