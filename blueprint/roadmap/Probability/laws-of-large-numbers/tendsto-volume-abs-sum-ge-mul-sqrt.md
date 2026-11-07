# Large deviations of mean-zero sums on the cube have vanishing measure

Let
$f : \mathbb{R} \to \mathbb{R}$ be square integrable on $[0,1]$ with $\int_0^1 f = 0$ and
$\int_0^1 |f|^2 > 0$, and let $(a_n)_{n \in \mathbb{N}}$ be a sequence of positive reals with
$a_n \to \infty$. For each $n$ let

$$F_n = \{ (x_1, \dots, x_n) \in [0,1]^n : |f(x_1) + \cdots + f(x_n)| \ge a_n \sqrt{n} \}.$$

Then $m_n(F_n) \to 0$ as $n \to \infty$, where $m_n$ is Lebesgue measure on $\mathbb{R}^n$.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration; Classical measure theory), `benchmark/level2/ma_proofbench_l2_06.lean` at openbmb/ma-proofbench@31bab4c.
