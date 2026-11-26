# Basic block multiplicity

Let $q$ be a natural number and
$(d_0, m_0), \dots, (d_{k-1}, m_{k-1})$ a list of blocks, and put $p_i = \sum_{j < i} m_j d_j$.
The basic multiplicity of block $i$ is $N_i = \sum_{j=0}^{m_i - 1} q^{p_i + j d_i}$ when $i < k$,
and $N_i = 0$ when $i \ge k$.
