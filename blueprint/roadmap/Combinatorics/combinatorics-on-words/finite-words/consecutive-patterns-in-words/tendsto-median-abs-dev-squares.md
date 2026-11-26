# Median absolute deviation of the squares

The following holds. For $n \in \mathbb{N}$ let $A_n = (1^2, 2^2, \dots, n^2)$, let $M_n = \operatorname{med}(A_n)$, and let

$$a_n = \operatorname{med}\bigl(\lvert 1^2 - M_n \rvert, \lvert 2^2 - M_n \rvert, \dots, \lvert n^2 - M_n \rvert\bigr)$$

be the median absolute deviation of $A_n$, with deviations counted with multiplicity. Here the median of a list with sorted entries $s_0 \le \dots \le s_{L-1}$ is $\frac{1}{2}\bigl(s_{\lfloor (L-1)/2 \rfloor} + s_{\lfloor L/2 \rfloor}\bigr)$, and $0$ for the empty list. Then

$$\lim_{n \to \infty} \frac{a_n}{n^2} = \frac{\sqrt{3}}{8}.$$

## Sources

- Sela Fried, "Proofs of Several Conjectures From the OEIS", Journal of Integer Sequences 28 (2025), Article 25.4.3, Theorem 8.
