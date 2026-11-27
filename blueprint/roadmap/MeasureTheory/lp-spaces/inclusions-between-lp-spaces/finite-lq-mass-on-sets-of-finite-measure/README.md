# An L^p function with finite L^q mass on finite-measure sets is in L^q

Let $1 \le p < q < \infty$ and let $f : \mathbb{R} \to \mathbb{R}$ belong to $L^p(\mathbb{R})$. If
$\int_A |f|^q < \infty$ for every Borel set $A \subseteq \mathbb{R}$ of finite Lebesgue measure, then
$f \in L^q(\mathbb{R})$.

## Idea

Only large values on sets of finite measure can keep an $L^p$ function out of $L^q$ for $q > p$. Take a
Borel function equal to $f$ almost everywhere. The set $A$ where its absolute value exceeds $1$ is
a Borel set of finite measure, by Markov's inequality applied to $|f|^p$, so the hypothesis bounds
$\int_A |f|^q$, while off $A$ almost everywhere $|f| \le 1$ and so $|f|^q \le |f|^p$.

## Statements

- [An $L^p$ function with finite $L^q$ mass on finite-measure sets is in $L^q$](mem-lp-of-mem-lp-of-lintegral-rpow-lt-to.md)
