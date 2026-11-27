# Level-1 Inequality

There is a universal constant $C$ such that every $f : \{-1, 1\}^n \to \{0, 1\}$ with mean
$\alpha = \mathbb{E}[f] \le 1/2$ satisfies

$$\mathbf{W}^1[f] = \sum_{|S| = 1} \hat f(S)^2 \le C\, \alpha^2 \log(1/\alpha).$$

Small subsets of the cube have little degree-1 Fourier weight. In additive combinatorics this is
Chang's inequality. For $\alpha = 0$ both sides are $0$ (with $\log(1/0)$ read as $0$). One can take $C = 2e$: this is
the Level-k Inequality at $k = 1$, whose hypothesis $1 \le 2 \ln(1/\alpha)$ holds since
$\alpha \le 1/2$ and $\ln 2 > 1/2$. This is the route of the source's Section 9.5; its
Section 5.4 proof uses a tail bound for linear forms instead.

## Sources

- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014 (arXiv:2105.10386), Level-1 Inequality, Section 5.4 (sharp form $2\alpha^2 \ln(1/\alpha)$ in Remark 5.28);
  generalized to the Level-k Inequalities in Section 9.5.
