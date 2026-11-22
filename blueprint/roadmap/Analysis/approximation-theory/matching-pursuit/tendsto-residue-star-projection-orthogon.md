# Convergence of matching pursuit

Let $H$ be a Hilbert space, $D = (g_\gamma)_{\gamma \in \Gamma}$ a dictionary of unit vectors, $V$ the closed linear span of $D$ and $W = V^\perp$. Let $0 < \alpha \le 1$, and suppose that at every step the selected index satisfies the weak greedy rule

$$|\langle g_{\gamma_n}, R^n f\rangle| \ge \alpha \sup_{\gamma \in \Gamma} |\langle g_\gamma, R^n f\rangle|$$

(equation (11)). Then $R^m f \to P_W f$ as $m \to \infty$ (S. Mallat and Z. Zhang, *Matching pursuits with time-frequency dictionaries*, IEEE Trans. Signal Process. 41 (1993), Theorem 1, equation (18)). Hence $P_V f = \sum_n \langle g_{\gamma_n}, R^n f\rangle g_{\gamma_n}$ and $\|P_V f\|^2 = \sum_n |\langle g_{\gamma_n}, R^n f\rangle|^2$ (equations (19)–(20)); for a complete dictionary, $V = H$, this recovers $f$ and its energy. The orthogonal complement of the span of the dictionary equals that of its closure, so either may be used.

## Informally uses

- [The residue energy is nonincreasing](norm-residue-succ-le.md): Mallat and Zhang's proof (Appendix A) uses equation (13) to see that $\|R^n f\|$ decreases to a limit.
- [Energy conservation of matching pursuit](norm-sq-eq-sum-add-norm-sq-residue.md): the same proof uses equation (17), $\sum_n |\langle R^n f, g_{\gamma_n}\rangle|^2 \le \|f\|^2$, to show that $(R^n f)$ is a Cauchy sequence.
