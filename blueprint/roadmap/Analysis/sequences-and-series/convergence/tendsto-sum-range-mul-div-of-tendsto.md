# Kronecker's lemma

Let $(b_n)_{n \ge 0}$ be a nondecreasing sequence of real numbers with
$b_n \to +\infty$, and let $(x_k)_{k \ge 0}$ be a real sequence whose series $\sum_k x_k$
converges. Then $\frac{1}{b_n} \sum_{k < n} b_k x_k \to 0$ as $n \to \infty$.

Proof: with $S_n = \sum_{k < n} x_k \to s$, summation by parts gives
$\sum_{k < n} b_k x_k = b_n (S_n - s) + s\, b_0 - \sum_{k < n} (b_{k+1} - b_k)(S_{k+1} - s)$, and
the last sum is $o(b_n)$ because its nonnegative weights add up to $b_n - b_0$ and
$S_{k+1} - s \to 0$ (Cesàro's lemma).

## Sources

- D. Williams, *Probability with Martingales*, Cambridge University Press (1991), §12.7, Kronecker's Lemma, stated there for weights $0 < b_n \uparrow \infty$ and the series $\sum_k x_k / b_k$: here $x_k$ plays the role of Williams's $x_k / b_k$, and the weights need not be positive.
