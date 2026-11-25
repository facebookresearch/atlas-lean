# The finite version $\dot T$ of $T$

Let $y = \langle y_1, \dots, y_n \rangle$ be a finite
word over $\{O_L, E_R, O_R, E_L\}$ and let $p_1 < p_2 < \cdots < p_k$ be the positions $j$ with
$y_j \in \{O_L, O_R\}$. Then $\dot T(y) = \langle t_1, \dots, t_{k-1} \rangle$ is the word over
$\{L, M, R\}$ (empty if $k \le 1$) given as follows. If $p_{i+1} = p_i + 1$, then $t_i$ is $L$
when $y_{p_i} = O_L$ and $R$ otherwise. If $p_{i+1} \ne p_i + 1$, then $t_i$ is $M$ when
$y_{p_i} \ne y_{p_{i+1}}$, $L$ when $y_{p_i} = y_{p_{i+1}} = O_R$, and $R$ when
$y_{p_i} = y_{p_{i+1}} = O_L$.

## Sources

- Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25 (2025), Article A78, Section 4.3 (definition of `Ṫ`).
