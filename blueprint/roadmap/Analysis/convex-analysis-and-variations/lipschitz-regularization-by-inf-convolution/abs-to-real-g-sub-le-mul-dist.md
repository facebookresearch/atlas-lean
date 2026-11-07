# The inf-convolution of a lower semicontinuous function is Lipschitz

Let $X$ be a metric
space with metric $d$, and let $f : X \to [0,\infty]$ be lower semicontinuous with $f(p) < \infty$
for at least one $p \in X$. For a natural number $n$ and $x \in X$ let

$$
g_n(x) = \inf\{f(p) + n\,d(x,p) : p \in X\} \in [0,\infty].
$$

Then $|g_n(x) - g_n(y)| \le n\,d(x,y)$ for every natural number $n$ (including $n = 0$) and all
$x, y \in X$.

Each $g_n(x)$ is finite, since $g_n(x) \le f(p) + n\,d(x,p)$ for the point $p$ with
$f(p) < \infty$, so the difference is one of real numbers.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functional analysis; Nonlinear functional analysis), `benchmark/level1/ma_proofbench_l1_36.lean` at openbmb/ma-proofbench@31bab4c.
