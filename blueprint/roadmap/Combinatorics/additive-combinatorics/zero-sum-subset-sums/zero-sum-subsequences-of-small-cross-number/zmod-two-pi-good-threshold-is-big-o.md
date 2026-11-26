# Threshold for good sequences in $\mathbb{Z}_2^d$

Write $\lg = \log_2$. Let $t$ be a threshold function, in $d$, for the probability
that a uniformly sampled labeled sequence of $s$ elements of $\mathbb{Z}_2^d$ is
good. The entries are independent uniform draws. Write $n = 2^d$. Then for every
$\varepsilon > 0$, $t(d) = O\left(n / (\lg \lg n)^{1-\varepsilon}\right)$ as
$d \to \infty$.

The cited paper uses a different law: its Section 3.1 configuration model is
uniform over size-$s$ multisets, not over labeled sequences. Counting repeated
entries gives the displayed bound directly in the labeled model.

## Sources

- Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in Abelian Groups*, INTEGERS 24 (2024), Article A93, Theorem 11 (the corresponding bound in the configuration model).
