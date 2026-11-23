# Ordered exact Hardy–Weinberg p-values are valid

Let $\mu$ be a measure on a measurable space $\Omega$, let $N$ and $n_A \le 2N$ be natural numbers,
and let $H : \Omega \to \mathbb{N}$ have [Levene's law](levene-measure.md) $\lambda_{N, n_A}$ under
$\mu$ (so $\mu$ is a probability measure). Then for every key $g : \mathbb{N} \to \mathbb{R}$ the
[ordered p-value](ordered-pvalue.md) $\omega \mapsto \mathrm{pv}_{L, g, n_A + 1}(H(\omega))$, with
$f = L(N, n_A, \cdot)$ and outcomes $0, \dots, n_A$, is a
[valid p-value](../../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/is-valid-pvalue.md)
under $\mu$: $\mu(\mathrm{pv} \le t) \le t$ for every $t \in [0, 1]$. No large-sample approximation
is involved (Wigginton, Cutler and Abecasis 2005; Lehmann and Romano 2005, Lemma 3.3.1).
