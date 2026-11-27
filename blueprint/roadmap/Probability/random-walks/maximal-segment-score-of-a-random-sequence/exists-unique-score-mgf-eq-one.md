# The Cramér (Karlin–Altschul) root of the score distribution

Let `q` be a probability vector on a finite alphabet with every `q_b > 0`, and `f` real scores with
negative mean, `∑_b q_b f(b) < 0`, and some positive score, `f(b) > 0` for some `b`. Then there is a
unique `θ > 0` with `∑_b q_b e^{θ f(b)} = 1`: the positive root of `m(θ) = 1` for the
[moment generating function](score-mgf.md) `m` (Karlin and Altschul 1990). It is the
[pair-score result](../../../Biology/bioinformatics/position-weight-matrices/exists-unique-pair-mgf-eq-one.md) applied to the
score `s(a, b) = f(a)`.
