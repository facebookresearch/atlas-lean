# Rail Clamp

The memoryless rail clamp with the closed endpoint convention:
`max vmin (min vmax x)`. Values at or below `vmin` give `vmin`,
values in the closed interval `[vmin, vmax]` are unchanged
(endpoints included), values at or above `vmax` give `vmax`.
Local to this leaf by design; see the header for why this is not a
generic saturation definition.
