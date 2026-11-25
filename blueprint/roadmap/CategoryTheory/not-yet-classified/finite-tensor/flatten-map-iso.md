# Flatten Map Iso

Strict equality `flatten ⋙ map F = map (map F) ⋙ flatten` as a natural iso.

This localizes the definitional equality of flatten and map; it is
`Iso.refl` because the two functors are definitionally equal.
