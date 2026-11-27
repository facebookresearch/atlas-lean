# Birkhoff pointwise ergodic theorem (ergodic case)

Let $\mu$ be a probability measure on a
measurable space $\alpha$, let $T : \alpha \to \alpha$ be ergodic with respect to $\mu$ (in
particular $T$ preserves $\mu$), and let $g : \alpha \to \mathbb{R}$ be $\mu$-integrable. Then for
$\mu$-almost every $x \in \alpha$, the Birkhoff averages $\frac{1}{n} \sum_{k=0}^{n-1} g(T^k x)$
converge to $\int g \, d\mu$ as $n \to \infty$.

This is the ergodic case; for a map preserving a finite measure the limit is in general the conditional
expectation of $g$ given the σ-algebra of invariant sets ([Birkhoff's pointwise ergodic theorem](tendsto-birkhoff-average-cond-exp-ae.md)).

## Sources

- G. D. Birkhoff, *Proof of the ergodic theorem*, Proc. Natl. Acad. Sci. USA 17 (1931), 656–660.
- P. Walters, *An Introduction to Ergodic Theory*, Graduate Texts in Mathematics 79, Springer (1982), Theorem 1.14.
