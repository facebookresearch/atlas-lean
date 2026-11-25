# Bonami Lemma

If $f : \{-1, 1\}^n \to \mathbb{R}$ has degree at most $k$ (every Fourier coefficient
$\hat f(S)$ with $|S| > k$ vanishes), then

$$\|f\|_4 \le \sqrt{3}^{\,k}\, \|f\|_2, \qquad\text{equivalently}\qquad
\mathbb{E}[f^4] \le 9^k\, \mathbb{E}[f^2]^2.$$

Low-degree polynomials of uniform random bits are "reasonable" random variables. The source proves
the lemma by a short induction on $n$ using $f = x_n D_n f + E_n f$. Alternatively, apply
the $(2,4)$-hypercontractivity bound $\|T_{1/\sqrt3}\, g\|_4 \le \|g\|_2$ to $g = T_{\sqrt3} f$, for which
$T_{1/\sqrt3}\, g = f$ and $\|g\|_2^2 = \sum_S 3^{|S|} \hat f(S)^2 \le 3^k \|f\|_2^2$. The statement above is the
fourth-power form.

## Sources

- A. Bonami, "Étude des coefficients de Fourier des fonctions de $L^p(G)$", *Ann. Inst. Fourier*
  20 (1970), 335–402.
- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014 (arXiv:2105.10386), Bonami Lemma, introduction of Chapter 9, proved in Section 9.1.
