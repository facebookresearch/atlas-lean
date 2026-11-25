# For a rotation, the normal component of X × V is x vy − y vx

For every rotation matrix `Q ∈ SO(3)`, real functions `x, y, vx, vy` of time and time `t`, with the
spatial position `X = Q (x(t), y(t), 0)` and velocity `V = Q (vx(t), vy(t), 0)`
([spatial states](spatial-state.md)), the component of the specific angular momentum `X × V` along
the oriented normal `Q e₃` of the orbit plane, `e₃ = (0, 0, 1)`, is the planar signed angular
momentum: `(X × V) · (Q e₃) = x(t) vy(t) − y(t) vx(t)`. A rotation keeps the orientation of the
plane.
