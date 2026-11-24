# TransSort 1.5-approximation and diameter

**TransSort 1.5-approximation and diameter** (Bafna-Pevzner 1998,
Corollaries 6.10-6.11): same hypotheses as `transposition_lower_bound`,
plus every TransSort run sorting within three quarters of the breakpoint
defect (`hsort`: `4 * len ≤ 3 * ((n+1) - c_odd)`), the distance
characterization (`hd_le`), and at least one odd cycle (`hodd`).
Conclusions: the run bound and the diameter bound `4 * d(π) ≤ 3 * n`.

## Sources

- Bafna-Pevzner (1998), Corollaries 6.10-6.11.
