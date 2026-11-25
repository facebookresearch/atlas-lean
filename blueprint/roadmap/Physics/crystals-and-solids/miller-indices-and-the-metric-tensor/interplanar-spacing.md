# Interplanar spacing of a family of lattice planes

For a [Bravais lattice](../bravais-lattices/bravais-lattice.md) and Miller indices `h ∈ ℤ³`, the
interplanar spacing is `d_h = 1 / ‖g_h‖`, where `g_h` is the
[reciprocal-lattice vector](reciprocal-vector.md) of `h`. For `g_h ≠ 0`, the shift `g_h / ‖g_h‖²`
carries each [plane](lattice-plane.md) of the family `h` to the next ([shift](plane-shift-mem.md))
and has length `d_h` ([length](plane-shift-norm.md)), and `d_h` bounds the distance between the
planes `n = 0` and `n = 1` from below ([distance bound](plane-dist-ge.md)). For `h = 0` there is no
family of planes, and the convention `1 / 0 = 0` gives `d_0 = 0`.
