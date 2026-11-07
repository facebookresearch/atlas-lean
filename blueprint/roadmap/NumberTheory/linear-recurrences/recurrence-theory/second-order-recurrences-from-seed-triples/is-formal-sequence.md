# Formal sequence from a seed triplet

Let $F$ be a field and $a, b, c \in F$. A sequence
$u : \mathbb{N} \to F$ is a formal sequence with seed triplet $(a, b, c)$ when $b \neq 0$,
$u_0 = a$, $u_1 = b$, $u_2 = c$, and for every $n \ge 0$

$$u_{n+2} = \alpha u_{n+1} - u_n + \beta,$$

where $\alpha = \frac{ab + bc + ca}{b^2} - 1$ and $\beta = \frac{b^2 - ac}{b}$ are the
coefficient and the constant term of the formal-sequence recurrence.

## Sources

- statement `jis_50a05fd3a5b6b4a1865a61bb`, concept `jis_sem_1ce947826a0dceb6fde5b7f2`, in <https://cs.uwaterloo.ca/journals/JIS/VOL23/Kocik/kocik5.tex>, lines 482–499. Source SHA-256: `f216e1e1606af32792c37505ee832c53db0244b0c93f934f34619996b1aa1746`; raw block SHA-256: `9665499a711e4ccc50f15a8b66c8cc5e643123774d2a19478a2e7605e8d72a4d`.
