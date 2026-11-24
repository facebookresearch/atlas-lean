# Decrement cursor In Range

Decrementing an existing positive cell index remains a valid cursor.  The
strictly-positive premise is essential: decrementing cell zero would create a
one-before-beginning pointer, which this model does not call valid.
