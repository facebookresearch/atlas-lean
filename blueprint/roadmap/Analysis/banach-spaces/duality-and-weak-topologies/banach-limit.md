# Existence of Banach limits

There is a continuous linear functional $L$ on the real Banach
space $\ell^\infty$ of bounded real sequences with the supremum norm such that $L(f) \ge 0$
whenever $f_n \ge 0$ for every $n$, $L$ maps the constant sequence $1$ to $1$, $L(f) = L(g)$
whenever $g_n = f_{n+1}$ for every $n$, and $L(f) = l$ whenever the sequence $f_n$ converges
to $l$.

## Sources

- S. Banach, Theorie des operations lineaires, 1932, definition of generalised limit; G. Lorentz, Acta Math. 80 (1948) 167-190; Lean formalizes ℓ∞ via `BoundedContinuousFunction ℕ ℝ` and real field `ℝ` with all four classical axioms.
