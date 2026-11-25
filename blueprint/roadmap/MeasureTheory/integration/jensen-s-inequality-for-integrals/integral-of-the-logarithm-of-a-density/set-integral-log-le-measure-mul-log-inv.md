# Upper bound for the integral of the logarithm of a probability density over a set

Let
$\mu$ be a measure on a measurable space $X$ and let $f : X \to \mathbb{R}$ be integrable with
respect to $\mu$, with $f(x) > 0$ for every $x \in X$ and $\int_X f\,d\mu = 1$. Then for every
measurable set $E \subseteq X$ with $0 < \mu(E) < \infty$ such that $\log f$ is integrable on $E$,

$$
\int_E \log f\,d\mu \le \mu(E)\log\frac{1}{\mu(E)}.
$$

The integrability of $\log f$ on $E$ is assumed so that the statement is real-valued: the
positive part of $\log f$ is integrable on $E$ (since $(\log f)^{+}\le f$), so if $\log f$
is not integrable on $E$ then $\int_E(\log f)\,d\mu=-\infty$ and the inequality holds in
$\mathbb{R}\cup\{-\infty\}$.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Measure and integration; Classical measure theory), problem `ma_proofbench_l1_82`.
