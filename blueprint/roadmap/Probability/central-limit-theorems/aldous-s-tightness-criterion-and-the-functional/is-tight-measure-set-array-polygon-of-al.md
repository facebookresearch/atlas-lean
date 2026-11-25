# Aldous's tightness criterion

**Aldous's tightness criterion** (continuous-limit form, for triangular arrays).

Let row `n` of the array `ξ` be adapted to the filtration `𝓕 n` (`ξ n i` is
`𝓕 n (i + 1)`-measurable). If the largest increment of row `n` tends to `0` in probability and
the partial sums satisfy Aldous's condition (`AldousCondition`), then the laws of the polygonal
processes `arrayPolygon n ξ` on `C([0,1])` are tight.

## Sources

- Jacod–Shiryaev (2003), Theorem VI.4.5 (Aldous's criterion for tightness in `D`) together with Proposition VI.3.26 (tightness in `D` plus vanishing jumps is `C`-tightness); Aldous (1978). The paths start at `0`, so the compact-containment condition (i) of VI.4.5 is not needed. The proof follows Jacod–Shiryaev's: the successive `ε`-oscillation times are stopping times; Aldous's condition makes each short oscillation block unlikely, Markov's inequality on the number of short blocks bounds the number of oscillations, and a path with few oscillations, long blocks and small steps has a small modulus of continuity (`isTightMeasureSet_of_modulus`).
