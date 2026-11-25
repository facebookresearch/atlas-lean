# Wardrop flows against a scaled demand

Let $f$ be a Wardrop equilibrium that is feasible for the demand $r$, let $c \in \mathbb R$, and
let $g$ be a flow feasible for the demand $c\, r$. Then

$$c \sum_P \ell_P(f)\, f_P \le \sum_P \ell_P(f)\, g_P .$$

Each commodity $i$ with $r_i > 0$ has a common latency $L_i$ on its flow paths, so the left side
is $c \sum_i L_i r_i$ (Lemma 2.3 of Roughgarden–Tardos), while every path of $i$ has latency at
least $L_i$ under $f$.

## Sources

- T. Roughgarden and É. Tardos, "How bad is selfish routing?", J. ACM 49(2) (2002), 236–259, Lemma 2.3 and proof of Theorem 3.1.
