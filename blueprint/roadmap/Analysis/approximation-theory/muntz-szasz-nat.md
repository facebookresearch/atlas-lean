# Müntz–Szász theorem for integer exponents

Let $\Lambda : \mathbb{N} \to \mathbb{N}$ be
strictly increasing with $\Lambda(0) = 0$. The real linear span of the monomials
$x \mapsto x^{\Lambda(n)}$, $n \in \mathbb{N}$, restricted to $[0, 1]$, is dense in
$C([0, 1], \mathbb{R})$ with the uniform norm if and only if the series
$\sum_{n \ge 0} 1/\Lambda(n+1)$ diverges, that is, the sequence
$(1/\Lambda(n+1))_{n \in \mathbb{N}}$ is not summable.

## Sources

- C. Müntz, Festschrift H. A. Schwarz 1914 303-312 and O. Szász, Math. Ann. 77 (1916) 482-496, Müntz-Szász theorem; Rudin Real & Complex; Lean states integer-exponent `ℕ→ℕ` `StrictMono` with `0∈range` case as closure `= ⊤` iff non-summable reciprocals.
