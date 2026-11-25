# Zeilberger's lemma for gamma vectors

Let $n$ be a natural number, let
$\gamma_0, \gamma_1, \gamma_2, \dots$ be rational numbers, and let $h \in \mathbb{Q}[x]$ be the
polynomial $h(x) = \sum_{j=0}^{\lfloor n/2 \rfloor} \gamma_j \, x^j (1 + x)^{n - 2j}$. Let
$c(x) = \sum_{m \ge 0} C_m x^m \in \mathbb{Q}[[x]]$ be the generating function of the Catalan
numbers $C_m$. Then for every natural number $k \le \lfloor n/2 \rfloor$, the number $\gamma_k$
is the coefficient of $x^k$ in the power series $h(x \, c(x)^2) \cdot c(x)^{-n}$.

## Sources

- Paul Barry, "The γ-Vectors of Pascal-like Triangles Defined by Riordan Arrays", Journal of Integer Sequences 22 (2019), Article 19.1.4, Proposition 10 (Zeilberger's Lemma), with the setup and notation of Section 1, <https://cs.uwaterloo.ca/journals/JIS/VOL22/Barry2/barry402.pdf>. Here $c(x) = (1 - \sqrt{1 - 4x})/(2x)$ is the generating function of the Catalan numbers $C_n = \frac{1}{n+1}\binom{2n}{n}$ (A000108). The display recalled just before Proposition 10 prints $\gamma_n$ on both sides; the statement follows Proposition 10.
