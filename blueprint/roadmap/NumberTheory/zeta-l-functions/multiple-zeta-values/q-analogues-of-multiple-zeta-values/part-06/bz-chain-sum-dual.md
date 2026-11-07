# Combinatorial form of Bradley–Zhao duality

For a list of blocks
$(s_1, w_1), \dots, (s_r, w_r)$ of positive integers and an integer $N \ge 1$, let
$S_N((s_1, w_1), \dots, (s_r, w_r))$ be the sum of $\binom{j_1}{w_1} \cdots \binom{j_r}{w_r}$
over all strictly decreasing chains $N + 1 > a_1 > \dots > a_n > 0$ of length
$n = s_1 + \dots + s_r$ and all multiplicities $c_1, \dots, c_n \ge 0$ with
$a_1 c_1 + \dots + a_n c_n = N$, where the chain is cut into consecutive blocks of lengths
$s_1, \dots, s_r$ and $j_t$ is the multiplicity of the first entry of block $t$. Let $r \ge 1$
and $k_1, \dots, k_r, d_1, \dots, d_r \ge 1$. Then

$$S_N((d_1, k_1), \dots, (d_r, k_r)) = S_N((k_r, d_r), \dots, (k_1, d_1)).$$

The bound $N + 1$ loses nothing: since $w_1 \ge 1$, a nonzero term has $j_1 \ge 1$ and hence
$a_1 \le N$.

## Sources

- arXiv:2111.00051, Theorem 4.18; the record's formula is garbled and is read from there, and the paper's closing remark (equivalence with BZ duality) is not part of this statement.
- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, Theorem 1 (`integers-2024-A6-thm-1`).
