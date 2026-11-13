# Uniqueness of the even-power shift in Catalan asymptotics

Let
$C_n = \binom{2n}{n} / (n + 1)$ be the $n$-th Catalan number. For a real number $\alpha$, there is
a real sequence $(a_k)_{k \ge 0}$ with $a_{2k+1} = 0$ for every $k$ such that, for every
$N \ge 0$, the difference
$C_n \sqrt{\pi} \, (n + \alpha)^{3/2} / 4^n - \sum_{k=0}^{N} a_k (n + \alpha)^{-k}$ is
$o\left((n + \alpha)^{-N}\right)$ as $n \to \infty$, if and only if $\alpha = 3/4$.

Elezović phrases this as the expansion "containing only odd terms"; the condition meant is that
the odd-indexed coefficients vanish: his displayed series for $\alpha = 3/4$ has only even powers,
and his proof obtains $\alpha = 3/4$ by setting the first odd coefficient to zero.

Proof: The reverse implication exponentiates the all-orders logarithmic expansion of the Catalan
numbers and uses the reflection symmetry of the Bernoulli polynomials to eliminate odd powers. The
first logarithmic coefficient gives uniqueness, following Elezović.

## Sources

- Neven Elezović, "Asymptotic Expansions of Central Binomial Coefficients and Catalan Numbers," Journal of Integer Sequences 17 (2014), Article 14.2.1, Corollary, lines 568–578, https://cs.uwaterloo.ca/journals/JIS/VOL17/Elezovic/elezovic5.tex
