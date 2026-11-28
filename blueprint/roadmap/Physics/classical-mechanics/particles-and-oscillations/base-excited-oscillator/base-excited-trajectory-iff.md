# For m > 0, plant trajectories are the relative-equation solutions

Let `m > 0` and let `c` and `k` be real numbers. For real functions `u`, `v`, `p` and `a_g` of
time, the following are equivalent:

- the curve `s ↦ (u(s), v(s))` is a trajectory of the linear plant driven by
  `s ↦ (p(s), a_g(s))`: at every time `t` it has derivative
  `A (u(t), v(t)) + B (p(t), a_g(t))`, with the [state matrix](base-excited-a.md)
  `A = [[0, 1], [-(k / m), -(c / m)]]` and the [input matrix](base-excited-b.md)
  `B = [[0, 0], [1 / m, -1]]`;
- at every time `t`, `u` has derivative `v(t)`, and `v` has a derivative `a` at `t` with
  `m a + c v(t) + k u(t) = p(t) - m a_g(t)`.

Then `v = u'` at every time and `a = u''(t)`, so the second condition says that `u` solves the
relative equation `m u'' + c u' + k u = p - m a_g` at every time, with a classical second
derivative; no continuity of `p`, `a_g` or `u''` is assumed. In the physical reading `c ≥ 0` and
`k > 0`; the equivalence holds for all real `c` and `k`. At `m = 0` it fails in general: with the
convention `u / 0 = 0` the matrices then lose the force and stiffness terms.
