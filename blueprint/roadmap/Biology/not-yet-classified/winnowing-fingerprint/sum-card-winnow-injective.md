# Expected number of winnowing fingerprints, i.i.d. uniform hashes without ties

**Expected number of winnowing fingerprints, i.i.d. uniform hashes without ties** (Schleimer,
Wilkerson and Aiken 2003, Section 3.1, with the source's no-ties assumption made exact): for a
finite linear order `H`, `n ≥ w ≥ 1` and `n ≤ |H|` (so that injective hash sequences exist),
the average of `#winnow h` over the injective `h : Fin n → H` (i.i.d. uniform hashes conditioned
on being distinct) is `1 + 2 (n - w) / (w + 1)`:
`(∑_{h injective} #winnow h) · (w + 1) = #{h injective} · ((w + 1) + 2 (n - w))`.

## Sources

- Schleimer, Wilkerson and Aiken (2003), Section 3.1.
