# The z-transform: region of convergence, shifts and convolution

For a sequence $x : \mathbb{Z} \to \mathbb{C}$ and $z \in \mathbb{C} \setminus \{0\}$, the z-transform is $X(z) = \sum_{n \in \mathbb{Z}} x_n z^{-n}$, taken where the series converges absolutely. Those $z$ form its region of convergence $\mathrm{ROC}_x$. Whether $z \in \mathrm{ROC}_x$ depends only on $|z|$, and the radii $|z|$ that occur form an interval: if $r_1 < r < r_2$ and $r_1, r_2$ occur, then $r^{-n} \le r_1^{-n}$ for $n \ge 0$ and $r^{-n} \le r_2^{-n}$ for $n < 0$, so $r$ occurs. Hence $\mathrm{ROC}_x$ is empty, a circle, or an annulus between radii $0 \le r_- < r_+ \le \infty$ that may contain either boundary circle.

1. **Geometric sequences.** Let $\alpha \ne 0$. The right-sided sequence $x_n = \alpha^n$ for $n \ge 0$, $x_n = 0$ for $n < 0$, has $\mathrm{ROC}_x = \{|z| > |\alpha|\}$ and $X(z) = \frac{1}{1 - \alpha z^{-1}} = \frac{z}{z - \alpha}$ there. The left-sided sequence $y_n = -\alpha^n$ for $n \le -1$, $y_n = 0$ for $n \ge 0$, has $\mathrm{ROC}_y = \{0 < |z| < |\alpha|\}$ and $Y(z) = \frac{z}{z - \alpha}$ there. The two transforms are given by the same expression on disjoint regions, so a transform determines its sequence only together with its region of convergence.
2. **Shift.** For $n_0 \in \mathbb{Z}$, the sequence $(x_{n - n_0})_n$ has the same region of convergence in $\mathbb{C} \setminus \{0\}$ and transform $z^{-n_0} X(z)$.
3. **Convolution.** If $z \in \mathrm{ROC}_h \cap \mathrm{ROC}_x$, then for every $n$ the series $(h * x)_n = \sum_{k} h_k x_{n-k}$ converges absolutely, $z \in \mathrm{ROC}_{h * x}$, and the transform of $h * x$ at $z$ is $H(z) X(z)$.
4. **One-sided transform.** Put $X_+(z) = \sum_{n \ge 0} x_n z^{-n}$, the transform of $(x_n \mathbf{1}_{n \ge 0})_n$, wherever $\sum_{n \ge 0} |x_n| |z|^{-n} < \infty$. There the advanced sequence $x'_n = x_{n+1}$ satisfies $X'_+(z) = z\,(X_+(z) - x_0)$. For one-sided sequences the convolution of part 3 is the finite sum $\sum_{k=0}^{n} h_k x_{n-k}$, with one-sided transform $H_+(z) X_+(z)$ wherever both one-sided series converge absolutely.

Part 1 sums geometric series: $\sum_{n \ge 0} (\alpha/z)^n$ converges absolutely exactly when $|z| > |\alpha|$, and $-\sum_{m \ge 1} (z/\alpha)^m$ exactly when $|z| < |\alpha|$. Part 2 reindexes. Part 3 is Fubini for the absolutely summable double series $\sum_n \sum_k h_k z^{-k} x_{n-k} z^{-(n-k)}$. Part 4 reindexes $\sum_{n \ge 0} x_{n+1} z^{-n} = z \sum_{m \ge 1} x_m z^{-m}$, and applies part 3 to one-sided sequences.

## Depends on

- [Convolution of sequences on the integers](../../banach-spaces/sequence-spaces/convolution-on-p/int-conv.md): the convolution $h * x$ of part 3

## Sources

- M. Vetterli, J. Kovačević and V. K. Goyal, *Foundations of Signal Processing*, Cambridge University Press, 2014 (free version v1.1), <https://fourierandwavelets.org/FSP_v1.1_2014.pdf>, Section 3.5: Definition 3.12 (z-transform and region of convergence, p. 235), the right- and left-sided geometric sequences (3.128a)–(3.128b) (pp. 236–237), the shift property (3.137) (p. 241) and the convolution property with region of convergence containing $\mathrm{ROC}_h \cap \mathrm{ROC}_x$ (Example 3.23 and the table of z-transform properties, pp. 242–243).
