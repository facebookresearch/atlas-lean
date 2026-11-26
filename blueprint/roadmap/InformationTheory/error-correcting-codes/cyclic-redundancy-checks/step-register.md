# Single step of an unreflected serial CRC register

Let $r \in \mathbb{N}$, let $g$ be a width-$r$ taps word (specifying the monic binary modulus $M_g = X^r + P_g \in \mathbb{F}_2[X]$), let $w$ be the current width-$r$ register word, and let $b \in \{0, 1\}$ be the next payload bit. One unreflected serial CRC register step updates $w$ to

$$\mathrm{step}_{r, g}(w, b) = \mathrm{mulX}_g(w) \oplus \iota_r(b),$$

where $\mathrm{mulX}_g(w)$ shifts $w$ left by one bit within width $r$ and XORs with $g$ when $r \ge 1$ and the shifted-out most significant bit of $w$ is $1$, $\iota_r(b)$ places $b$ in bit $0$ (modulo $2^r$), and $\oplus$ is bitwise exclusive or.
