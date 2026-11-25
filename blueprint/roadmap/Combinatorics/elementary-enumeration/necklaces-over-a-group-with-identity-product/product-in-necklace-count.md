# Counting necklaces with product in a conjugation-closed set

Let $G$ be a finite group,
let $K \subseteq G$ be closed under conjugation ($g k g^{-1} \in K$ for all $g \in G$ and
$k \in K$), and let $n \ge 1$. The number of rotation orbits of $n$-tuples
$(x_1, \dots, x_n) \in G^n$ with $x_1 x_2 \cdots x_n \in K$ ($K$-product $n$-necklaces) is

$$\frac{1}{n} \sum_{d \mid n} \varphi(n/d)\, N_K(n/d)\, |G|^{d-1},$$

where $\varphi$ is Euler's totient function and $N_K(e)$ is the number of $a \in G$ with
$a^e \in K$.

The printed Theorem 22 has $N_K(n)$ in place of $N_K(n/d)$; the arXiv text (Theorem 8.3) has
$n/d$, and the printed formula fails for $G = S_3$, $K = \{1\}$, $n = 2$ ($5$ necklaces against
$14$).

## Sources

- Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*, Journal of Integer Sequences 29 (2026), Article 26.4.6, Theorem 22 (`jis-2026-26.4.6-thm-22`).
