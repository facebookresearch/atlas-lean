# Expectation over an iid score sequence of length `n`

Letters `w₀, …, w_{n-1}` are drawn
independently from the law `q` on the finite alphabet `β` (sequence likelihood `bgLik q w`, from
`Cslib.Bioinformatics.Motifs.PWM`) and scored by `f`; `scoreExpect q f n F` is the expectation of
the functional `F` of the score list `[f w₀, …, f w_{n-1}]`.
