# Decrease

Lower the key at a live handle. Only a strict parent-order violation initiates a cut and a
cascade. The cached minimum is updated by comparison, and the second output counts all cuts,
including the initiating one. The step rule requires that the new key not exceed the old.
