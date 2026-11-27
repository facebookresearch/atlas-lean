# Input bit as a fixed-width register word

For a register width $r \in \mathbb{N}$ and a payload bit $b \in \{0, 1\}$, the input word $\iota_r(b)$ is the width-$r$ binary word representing $1 \bmod 2^r$ if $b = 1$ and $0$ if $b = 0$. When $r > 0$, bit $0$ (the coefficient of $X^0$) equals $b$ and all higher bits are $0$; when $r = 0$, $\iota_0(b)$ is the unique empty $0$-bit word.
