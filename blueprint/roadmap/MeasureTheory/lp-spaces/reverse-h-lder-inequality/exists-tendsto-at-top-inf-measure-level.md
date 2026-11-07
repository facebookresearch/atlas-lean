# Uniformly large level sets under a reverse Hölder bound

Let $\mu$ be Lebesgue measure
on $[0,1]$, and let $f_0, f_1, f_2, \ldots : \mathbb{R} \to \mathbb{R}$ lie in $L^2(\mu)$ with
$\|f_n\|_{L^2(\mu)} \le 2024\,\|f_n\|_{L^1(\mu)}$ for every $n$ and
$\|f_n\|_{L^1(\mu)} \to \infty$ as $n \to \infty$. Then there is a sequence of real numbers
$y_n \to \infty$ such that

$$
\inf_n \mu(\{x : |f_n(x)| \ge y_n\}) > 0.
$$

The divergence hypothesis is the limit $\|f_n\|_{L^1(\mu)} \to \infty$ in $[0,\infty]$; the
formal source instead required $\|f_n\|_{L^1(\mu)} = \infty$ for all large $n$, which no function
in $L^2(\mu)$ satisfies, so its statement was vacuous.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration; Classical measure theory), `benchmark/level2/ma_proofbench_l2_04.lean` at openbmb/ma-proofbench@31bab4c, with the change above.
