# Peart–Woodson triple factorization of Riordan arrays

Let $b$ be an integer, let
$\varepsilon$, $\delta$ and $\lambda$ be real numbers, and let $g$ and $f$ be formal power series
over $\mathbb{R}$ with $g(0) = 1$ and $f(0) = 0$. Write $r_{n,k}$ for the coefficient of $x^n$
in $g f^k$, and suppose that for all natural numbers $n$ and $k$

$$r_{n+1,0} = (b + \varepsilon)\, r_{n,0} + (\lambda + \delta)\, r_{n,1},$$



$$r_{n+1,k+1} = r_{n,k} + b\, r_{n,k+1} + \lambda\, r_{n,k+2},$$

that is, the Riordan array $(g, f)$ has dot diagram
$[b + \varepsilon, \lambda + \delta; 1, b, \lambda]$. With the Riordan product
$(p_1, p_2) \ast (q_1, q_2) = (p_1 \cdot q_1(p_2),\, q_2(p_2))$, let
$P_b = \bigl(1/(1 - bx),\, x/(1 - bx)\bigr)$ and
$C_\lambda = \bigl(c(\lambda x^2),\, x\, c(\lambda x^2)\bigr)$, where
$c(x) = \sum_{m \ge 0} C_m x^m$ is the generating function of the Catalan numbers $C_m$, and let
$F_{\varepsilon,\delta} = \bigl(1/(1 - \varepsilon x - \delta x^2),\, x\bigr)$. Then
$(g, f) = (P_b \ast C_\lambda) \ast F_{\varepsilon,\delta}$.

## Sources

- Cameron and Nkwanta, Riordan multiplication at lines 113–117 and the dot-diagram recursions at lines 124–138.
- Naiomi T. Cameron and Asamoah Nkwanta, *On Some (Pseudo) Involutions in the Riordan Group*, Journal of Integer Sequences 8 (2005), Article 05.3.7, Triple Factorization theorem due to Peart and Woodson, line 339, reused in the proof at line 373, <https://cs.uwaterloo.ca/journals/JIS/VOL8/Cameron/cameron46.tex>.
