# Fibonacci complement value

Let $(F_i)_{i \ge 0}$ be the Fibonacci numbers with
$F_0 = 1$, $F_1 = 2$ and $F_{i+2} = F_{i+1} + F_i$. The Fibonacci complement value of a word
$w = w_{k-1} \cdots w_1 w_0$ of natural numbers, written most significant digit first, is the
integer $\operatorname{val}_{\mathcal{F}c}(w) = \sum_{i=0}^{k-1} w_i F_i - w_{k-1} F_k$ when
$k \ge 1$, and $0$ when $w$ is empty.

## Sources

- Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24 (2024), Article A112, Section 9.2.
