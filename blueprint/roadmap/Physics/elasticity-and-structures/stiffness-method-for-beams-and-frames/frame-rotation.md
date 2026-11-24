# Global-to-local transformation of a planar frame element

For real numbers `c` and `s`, the frame transformation is the 6 × 6 block-diagonal matrix `T` with
two copies of the block `[[c, s, 0], [-s, c, 0], [0, 0, 1]]`, acting on `(u1, v1, θ1, u2, v2, θ2)`:
at each end it maps the global translation `(u, v)` to the axial and transverse components
`(c u + s v, -s u + c v)` and leaves the rotation unchanged. In the physical reading `(c, s)` are
the direction cosines of the element axis in global coordinates, with `c² + s² = 1`.
