# Flip-flop parameter transformation

At distinct rates, the
oral curve for the tuple `(F, D, ka, V, CL)` equals the oral curve
for the flipped tuple
`(F * ka / (CL / V), D, CL / V, V, ka * V)`: the absorption and
elimination rates are exchanged, `D` and `V` are unchanged, and
bioavailability is transformed to `F * ka / (CL / V)`, not kept
fixed. Admissibility of the flipped tuple (`F * ka / (CL / V) ≤ 1`)
is a precondition (`hFflip`), not a conclusion. This proves
sufficiency of the transformed value; no necessity claim is made.
Equal rates are excluded (the
denominator vanishes; the limiting equal-rate form is different).
