# Birkhoff pointwise ergodic theorem (ergodic case)

Let $\mu$ be a probability measure on a
measurable space $\alpha$, let $T : \alpha \to \alpha$ be ergodic with respect to $\mu$ (in
particular $T$ preserves $\mu$), and let $g : \alpha \to \mathbb{R}$ be $\mu$-integrable. Then for
$\mu$-almost every $x \in \alpha$, the Birkhoff averages $\frac{1}{n} \sum_{k=0}^{n-1} g(T^k x)$
converge to $\int g \, d\mu$ as $n \to \infty$.

## Sources

- G. D. Birkhoff, Proc. Natl. Acad. Sci. USA 17 (1931); Walters, Intro to Ergodic Theory; Lean states ergodic case for ℝ-valued integrable functions while general theorem gives conditional expectation onto invariant σ-algebra.
