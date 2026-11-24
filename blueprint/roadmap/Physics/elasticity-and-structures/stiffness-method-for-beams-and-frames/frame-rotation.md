# Frame Rotation

Global-to-local planar frame transform for one element whose
local axial direction has global direction cosines `(c, s)`.
At each end it maps global translations `(u, v)` to axial and
transverse components `(c*u + s*v, -s*u + c*v)` and leaves the
in-plane rotation coordinate unchanged.
