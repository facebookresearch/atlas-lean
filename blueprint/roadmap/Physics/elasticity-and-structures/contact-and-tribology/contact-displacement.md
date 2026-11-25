# Displacement of a spring pressed against an obstacle

For real numbers `k` (stiffness), `g` (obstacle position) and `f` (load), the contact displacement
is `min(g, f / k)`. With the convention `a / 0 = 0`, it is `min(g, 0)` when `k = 0`; the intended
domain is `k > 0`, where it satisfies the
[complementarity conditions](contact-displacement-complementarity.md) of the contact problem.
