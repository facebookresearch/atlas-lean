# Müntz–Szász theorem for integer exponents

Let $\Lambda : \mathbb{N} \to \mathbb{N}$ be strictly increasing with $\Lambda(0) = 0$. The real linear
span of the monomials $x \mapsto x^{\Lambda(n)}$, $n \in \mathbb{N}$, restricted to $[0, 1]$, is dense
in $C([0, 1], \mathbb{R})$ with the uniform norm if and only if the series
$\sum_{n \ge 0} 1/\Lambda(n+1)$ diverges.

## Sources

- C. Müntz, *Über den Approximationssatz von Weierstrass*, in: Mathematische Abhandlungen Hermann
  Amandus Schwarz zu seinem fünfzigjährigen Doktorjubiläum gewidmet, Springer, 1914, 303–312.
- O. Szász, *Über die Approximation stetiger Funktionen durch lineare Aggregate von Potenzen*,
  Mathematische Annalen 77 (1916), 482–496.
- W. Rudin, *Real and Complex Analysis*, McGraw-Hill (the Müntz–Szász theorem). Lean states integer-exponent `ℕ→ℕ` `StrictMono` with `0∈range` case as closure `= ⊤` iff non-summable reciprocals.
