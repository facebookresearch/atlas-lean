# Trudi's partition sum

Let $R$ be a commutative semiring, let $s \in R$, let $n$ be a
natural number, and let $a : \mathbb{N} \to R$ (only $a_1, \dots, a_n$ enter). Trudi's
partition sum is

$$
\sum_{\alpha} s^{|\alpha|} \, m_n(\alpha) \, a_1^{\alpha_1} a_2^{\alpha_2} \cdots a_n^{\alpha_n},
$$

where $\alpha = (\alpha_1, \dots, \alpha_n)$ runs over the tuples of natural numbers with
$\alpha_1 + 2\alpha_2 + \cdots + n\alpha_n = n$, $|\alpha| = \alpha_1 + \cdots + \alpha_n$, and
$m_n(\alpha) = |\alpha|! / (\alpha_1! \cdots \alpha_n!)$ is the multinomial coefficient, taken in
$R$. Such a tuple records a partition of $n$ with $\alpha_i$ parts equal to $i$. For $n = 0$ the
sum has the single empty term and equals $1$.

## Sources

- Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Lemma 1 (notation `α̃`, `|α|`, `m_n(α)`).
