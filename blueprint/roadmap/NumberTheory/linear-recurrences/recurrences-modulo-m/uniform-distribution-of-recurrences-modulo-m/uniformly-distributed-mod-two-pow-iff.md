# Uniform distribution of recurrences modulo powers of two

Let $a, b$ be integers and $(w_n)_{n \ge 0}$ an integer sequence with $w_{n+2} = aw_{n+1} + bw_n$, and write $D = a^2 + 4b$. Let $b$ be odd and $e \ge 2$. Then $w$ is uniformly distributed modulo $2^e$ if and only if $2 \mid D$, $a \equiv 2 \pmod 4$, $b \equiv 3 \pmod 4$, $w_0 \not\equiv w_1 \pmod 2$ and $w$ is $2$-regular; in that case $h_w(2^e) = 2^e$, $\lambda_w(2)/2 = 1$ and $\lambda_w(2^e) = 2^e$. Here, for $m \ge 1$, $w$ is uniformly distributed modulo $m$ when $\lambda_w(m) > 0$ and every residue modulo $m$ occurs exactly $\lambda_w(m)/m$ times among $w_0, \dots, w_{\lambda_w(m)-1}$, $w$ is $p$-regular when $w_0 w_2 - w_1^2 \not\equiv 0 \pmod p$ (with $p = 2$), $\lambda_w(m)$ is the least $\ell > 0$ with $w_{n+\ell} \equiv w_n \pmod m$ for all $n$ ($0$ if none), and $h_w(m)$ is the least $f > 0$ such that $w_{n+f} \equiv M w_n \pmod m$ for all $n$ for some integer $M$ coprime to $m$ ($0$ if none).

## Sources

- L. Somer and M. Křížek, Generalization of a theorem of Vélez on uniform distribution in second-order linear recurrences, Integers 25 (2025), Article A1, Theorem 2.3 (iv).
