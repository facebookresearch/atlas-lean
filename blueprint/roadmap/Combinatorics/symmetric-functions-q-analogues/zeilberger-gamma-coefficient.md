# Zeilberger's lemma for gamma vectors

Let $n$ be a natural number, let
$\gamma_0, \gamma_1, \gamma_2, \dots$ be rational numbers, and let $h \in \mathbb{Q}[x]$ be the
polynomial $h(x) = \sum_{j=0}^{\lfloor n/2 \rfloor} \gamma_j \, x^j (1 + x)^{n - 2j}$. Let
$c(x) = \sum_{m \ge 0} C_m x^m \in \mathbb{Q}[[x]]$ be the generating function of the Catalan
numbers $C_m$. Then for every natural number $k \le \lfloor n/2 \rfloor$, the number $\gamma_k$
is the coefficient of $x^k$ in the power series $h(x \, c(x)^2) \cdot c(x)^{-n}$.

## Sources

- Paul Barry, "The γ-Vectors of Pascal-like Triangles Defined by Riordan Arrays", Journal of Integer Sequences 22 (2019), Article 19.1.4, Zeilberger's Lemma proposition lines 281–283, <https://cs.uwaterloo.ca/journals/JIS/VOL22/Barry2/barry402.tex>. The gamma-matrix setup and `h` notation use supporting lines 110–120; the Catalan generating function `c(x) = (1 - sqrt (1 - 4 * x)) / (2 * x)` has coefficients `C_n = (1 / (n + 1)) * choose (2 * n) n` (A000108). The malformed recalled display at source line 275 printing `gamma_n` on both sides is excluded; the correctly printed proposition with `h_n` on the left is formalized.
