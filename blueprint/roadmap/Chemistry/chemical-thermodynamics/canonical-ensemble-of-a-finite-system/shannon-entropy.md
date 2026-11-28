# Shannon entropy of a distribution

The Shannon entropy `H(p) = -∑ i, p i * log (p i)` of a probability distribution `p` on a finite set
(`p i ≥ 0`, `∑ i, p i = 1`). By the convention `log 0 = 0`, a state with `p i = 0` contributes `0`.
The formula accepts any real `p`; for other inputs it need not be an entropy (one state of weight
`2` gives `-2 log 2 < 0`), and a negative entry uses `log x = log |x|`.
