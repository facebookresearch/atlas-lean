# Overlap

`ov(s, t)` is the largest `k` with `k < |s|`, `k < |t|` and the last `k` letters of
`s` equal to the first `k` letters of `t` (so `s = u v`, `t = v w` with `|v| = k` and `u`, `w`
nonempty). Unlike `Cslib.Bioinformatics.Assembly.StringOverlap.overlap`, which allows
`k = min (|s|, |t|)`, it is a proper overlap, as in the source; MGREEDY's self-overlap `ov(s, s)`
needs this.
