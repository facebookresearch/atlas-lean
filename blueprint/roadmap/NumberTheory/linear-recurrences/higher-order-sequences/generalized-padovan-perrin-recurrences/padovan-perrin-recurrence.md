# Generalized Padovan–Perrin recurrence

Let $R$ be a commutative semiring, $k_1, k_2 \in R$
and $p, s \in \mathbb{N}$. The $([k]; p; s)$-generalized Padovan–Perrin recurrence is the linear
recurrence of order $s + p$ with coefficients $c_i = [i = 0] \, k_2 + [i = p] \, k_1$ for
$0 \le i < s + p$, where $[\cdot]$ is $1$ if the condition holds and $0$ otherwise: a sequence
$v \colon \mathbb{N} \to R$ solves it when $v_{n+s+p} = \sum_{i=0}^{s+p-1} c_i v_{n+i}$ for every
$n \ge 0$. For $s > 0$ this reads $v_{n+s+p} = k_1 v_{n+p} + k_2 v_n$, that is,
$v_n = k_1 v_{n-s} + k_2 v_{n-s-p}$ for $n \ge s + p$ (equation (1)).

## Sources

- Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino, *On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24 (2024), Article A49, equation (1).
