# The modular discriminant in terms of Eisenstein series

For $z$ in the upper half-plane let $q = e^{2\pi i z}$, let
$\eta(z) = e^{2\pi i z / 24} \prod_{n \ge 1} (1 - q^n)$ be the Dedekind eta function and $\Delta(z) = \eta(z)^{24}$
the modular discriminant, and for $k = 4, 6$ let

$$E_k(z) = \frac{1}{2} \sum_{\substack{(c, d) \in \mathbb{Z}^2 \\ \gcd(c, d) = 1}} \frac{1}{(c z + d)^k}$$

be the normalised Eisenstein series of level one and weight $k$. Then

$$\Delta(z) = \frac{E_4(z)^3 - E_6(z)^2}{1728}.$$

## Sources

- D. Zagier, *Elliptic modular forms and their applications*, in *The 1-2-3 of Modular Forms*,
  Universitext, Springer (2008), 1–103,
  <https://people.mpim-bonn.mpg.de/zagier/files/doi/10.1007/978-3-540-74119-0_1/fulltext.pdf>: §2.1, formulas (9)–(11)
  (the normalised Eisenstein series $E_k$ as a sum over coprime pairs, and $G_k = \zeta(k) E_k$); §2.4, the definition (22)
  of $\Delta$ and formula (23), $\Delta = \frac{1}{1728} (E_4^3 - E_6^2)$ (pp. 20–21).
