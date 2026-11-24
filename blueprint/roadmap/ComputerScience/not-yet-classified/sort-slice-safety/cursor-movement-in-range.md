# Cursor Movement In Range

An `advance` starts at a valid cursor and its signed displacement stays
between the distance back to zero and the distance forward to the permitted
one-past endpoint.  This states the arithmetic obligation independently of
the desired postcondition even though advancement emits no indexed access.
