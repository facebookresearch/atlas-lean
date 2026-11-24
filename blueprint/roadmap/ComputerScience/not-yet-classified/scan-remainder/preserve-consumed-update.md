# Preserve consumed update

A mutation confined to the already-consumed prefix preserves the exact
unscanned suffix.  Structural fields are named explicitly so callers cannot
silently change the interval described by the invariant.
