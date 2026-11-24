# Reading R C as a frequency is not dimensionally correct

The [law](rcas-frequency.md) `f = R C` between a frequency, a resistance and a capacitance is not
dimensionally correct: for some two choices of units and some values, it holds in one choice of
units and fails for the converted values. For example (the proof's witness), `f = 6`, `R = 2` and
`C = 3` satisfy it in SI units, while their values in the units of length, time, mass, charge and
temperature that are `2`, `3`, `5`, `7` and `11` times the SI units do not.
