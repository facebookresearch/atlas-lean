# The Cramér (Karlin–Altschul) root

**The Cramér (Karlin–Altschul) root** (Karlin and Altschul 1990): if the expected score is
negative, some score is positive, and every letter has positive probability (inherited from
`existsUnique_pairMGF_eq_one`), there is a unique `θ > 0` with `E[e^{θX}] = 1`. This is
`Cslib.Bioinformatics.Motifs.PWM.existsUnique_pairMGF_eq_one` applied to `s a b = f a`.
