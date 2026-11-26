# Trudi's partition sum as a sum over compositions

Let $R$ be a commutative semiring, let
$s \in R$, let $a_0, a_1, a_2, \dots$ be elements of $R$ and let $n \ge 0$. Trudi's partition sum

$$\sum_\alpha s^{|\alpha|} m_n(\alpha) \, a_1^{\alpha_1} a_2^{\alpha_2} \cdots a_n^{\alpha_n},$$

taken over the tuples $\alpha = (\alpha_1, \dots, \alpha_n)$ of nonnegative integers with
$\alpha_1 + 2\alpha_2 + \dots + n\alpha_n = n$, where $|\alpha| = \alpha_1 + \dots + \alpha_n$ and
$m_n(\alpha) = |\alpha|! / (\alpha_1! \cdots \alpha_n!)$, equals

$$\sum_c s^{\ell(c)} \, a_{c_1} a_{c_2} \cdots a_{c_{\ell(c)}},$$

where $c = (c_1, \dots, c_{\ell(c)})$ runs over the compositions of $n$, that is, the finite
sequences of positive integers with sum $n$, and $\ell(c)$ is the number of parts of $c$.

The multinomial coefficient $m_n(\alpha)$ counts the compositions of $n$ in which each part $i$
occurs $\alpha_i$ times.

## Sources

- Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Lemma 1 and the composition reading of `det(A_n)` in Section 3.
