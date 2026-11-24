# Advance Traced

Pointer advancement emits no indexed access.  `valuesPresent` remains an
explicit input because C advances the optional values pointer in the same
mode, but both pointer adjustments erase to the model's single cursor.
