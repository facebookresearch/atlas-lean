# An unbounded distinguisher decides residuosity

For a key whose element $y$ is not a square, the distinguisher that tests whether its challenge is a
square outputs $1$ on every $y x^2$ and never on $x^2$, so it has advantage $1$ in the
[residuosity experiment](qr-exp.md). Hence the hypothesis "every distinguisher has residuosity
advantage at most $\varepsilon$" forces $\varepsilon \ge 1$: in this concrete model, where every
function counts as a distinguisher, the theorems that assume it are vacuous.

## Informally uses

- [Encryptions of `0` are squares](is-square-encrypt-bit-false.md)
- [Encryptions of `1` are non-squares](not-is-square-encrypt-bit-true.md)
