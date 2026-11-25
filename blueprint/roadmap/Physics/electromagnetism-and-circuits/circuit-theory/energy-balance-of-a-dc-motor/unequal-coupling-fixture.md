# Example of a DC motor with unequal motor constants

Take `R = L = J = b = ke = 1`, `kt = 2`, constant `i = ω = 1`, `u = 2` and `τL = 1`. At every time
`t`:

- the armature equation `2 = 1 · 1 + 1 · 0 + 1 · 1` and the rotor equation
  `1 · 0 = 2 · 1 - 1 · 1 - 1` hold, the derivatives of the constants being `0`;
- the [stored energy](motor-energy.md) is constant, so its derivative is `0`;
- the reciprocal balance `u i - R i² - b ω² - τL ω` equals `-1`;
- adding the coupling residual `(kt - ke) i ω = 1` gives `0`, the derivative.
