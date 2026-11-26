# Banaszczyk's shifted Gaussian tail bound

Let $L$ be a full-rank lattice in dimension $n$ (including $n = 0$), $s > 0$, $v$ any shift and $c > 1/\sqrt{2\pi}$. Then

$$\rho_{s}\bigl(\{x \in L - v : \|x\| > c\,s\sqrt{n}\}\bigr) < \bigl(c\sqrt{2\pi e}\,e^{-\pi c^2}\bigr)^{n}\,\rho_s(L).$$

At $c = 1$ the factor is below $(1/4)^n$ for $n \ge 1$. Banaszczyk (1993, Lemma 1.5) proves this bound for $v \in L$ and, for arbitrary $v$, with an extra factor $2$ on the right; the factor-free form for every shift follows from the two steps of the proof sketch, both of which hold for every $v$.

## Proof sketch

For $t \in (0, 1)$, compare $\rho_s$ with $\rho_{s/\sqrt{t}}$ on the tail, bound $\rho_{s/\sqrt t}(L - v)$ by $\rho_{s/\sqrt t}(L)$ (mass is maximized at the origin) and by $t^{-n/2}\rho_s(L)$ by Poisson summation, then optimize $t = 1/(2\pi c^2)$.

## Depends on

- [Gaussian function, Gaussian mass and discrete Gaussian on a lattice](discrete-gaussian-on-a-lattice.md)

## Proof depends on

- [Shifted lattice Gaussian mass is maximized at the origin](shifted-gaussian-mass-maximized-at-origin.md)

## Sources

- W. Banaszczyk, "New Bounds in Some Transference Theorems in the Geometry of Numbers", Mathematische Annalen 296, 1993.
- D. Micciancio and O. Regev, "Worst-Case to Average-Case Reductions Based on Gaussian Measures", SIAM Journal on Computing 37(1), 2007.
- O. Regev, "On Lattices, Learning with Errors, Random Linear Codes, and Cryptography", Journal of the ACM 56(6), 2009.
