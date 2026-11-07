# Watson's lemma for Laplace integrals

Let $g : \mathbb{R} \to \mathbb{R}$ and let
$(c_k)_{k \ge 1}$ be real numbers such that for every $N \ge 0$,
$g(s) - \sum_{k=1}^{N} c_k s^k = O(s^{N+1})$ as $s \to 0^+$. Suppose there is $m_0 \in \mathbb{R}$
such that $s \mapsto g(s) e^{-ms}$ is integrable on $(0, \infty)$ for every $m \ge m_0$. Then
for every $N \ge 0$,
$\int_0^\infty g(s) e^{-ms} \, ds - \sum_{k=1}^{N} k! \, c_k / m^{k+1} = O(1 / m^{N+2})$ as
$m \to \infty$.

The case $N = 0$ of the hypothesis says $g(s) = O(s)$ as $s \to 0^+$: the expansion of $g$ has no
constant term.

Grounded record: `jis_grounded_f44808e9542400b9602c4bfc`
Concept: `jis_dep_4b8d33719e173348274b207f`

## Sources

- `https://cs.uwaterloo.ca/journals/JIS/VOL14/Nemes/nemes4.tex`, lines 142-151 File SHA-256: `4420f4c929622a46f0e5623054b7cc4a699802cfb111b4dce5d1922af1e4c1d7` Span SHA-256: `30a175909268f0c6c372ad6dba97f6edb373a35cf7eb26ecb5a0c0212eec8ee6` Counts: 2 mentions / 1 paper / 1 proof use. Proves `Wanted` entry `watson_laplace_integral_asymptotic`.
