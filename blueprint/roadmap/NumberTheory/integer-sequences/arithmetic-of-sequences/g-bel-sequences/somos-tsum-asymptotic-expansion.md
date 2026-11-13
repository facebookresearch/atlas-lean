# Sondow–Hadjicostas asymptotic expansion

Let $k \ge 2$ be a natural number. For $j \ge 1$
put $S_j = \sum_{i \ge 1} i^j / k^i$ and $b_j = (-1)^{j-1} S_j / j$, and for $r \ge 0$ let

$$a_r = \sum_{m_1 + 2 m_2 + \dots + r m_r = r} \ \prod_{j=1}^{r} \frac{b_j^{m_j}}{m_j!},$$

where the sum runs over the tuples $(m_1, \dots, m_r)$ of natural numbers satisfying the
constraint. For $n \in \mathbb{N}$ let $E(n) = \exp\bigl(\sum_{s \ge 1} \log(s + n) / k^s\bigr)$
and, for a natural number $R$, let $P_R(n) = 1 + \sum_{r=1}^{R} a_r / n^r$. Then for every
natural number $R$,

$$E(n) - n^{1/(k-1)} P_R(n) = O\bigl(n^{1/(k-1)} / n^{R+1}\bigr)$$

as $n \to \infty$ through the natural numbers.

In the paper $S_j$ appears as $A_j(k) / (k - 1)^{j+1}$, with $A_j$ the Eulerian polynomial.

## Sources

- Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024), Article 24.8.1, Theorem 15, quoting Sondow and Hadjicostas (2007), Theorem 9 and Lemma 1 (`jis-2024-24.8.1-thm-15`).
