# Bañuelos–Janakiraman upper bound for the Beurling–Ahlfors transform

For a function
$f : \mathbb{C} \to \mathbb{C}$ let $Bf(z)$ be the limit as $\varepsilon \to 0^+$ of
$-\frac{1}{\pi} \int_{|w - z| > \varepsilon} \frac{f(w)}{(z - w)^2} \, dA(w)$, where $dA$ is
Lebesgue area measure (a junk value where the limit does not exist), and for real $p > 1$ let
$p^* = \max(p, p/(p - 1))$. For every real $p > 1$ and every almost everywhere strongly measurable
$f : \mathbb{C} \to \mathbb{C}$, $\|Bf\|_{L^p} \le 1.575\,(p^* - 1)\,\|f\|_{L^p}$, with the
$L^p$ norms taken in $[0, \infty]$.

## Sources

- Bañuelos and Janakiraman, *Lp-bounds for the Beurling--Ahlfors transform*, Trans. Amer. Math. Soc. 360 (2008): `‖B‖ₚ ≤ 1.575 (p* - 1)` for all `1 < p`. Stated as the actual finite exponential bound (an admissible `L^p` bound constant), not as an inequality for the totalized infimum; combined with `beurlingNorm_le_of_isBound` (and `0 ≤ 1.575 * (pstar p - 1)`, from `two_le_pstar`) it yields `beurlingNorm p ≤ 1.575 * (pstar p - 1)`. Known literature result; its proof is not supplied here.
