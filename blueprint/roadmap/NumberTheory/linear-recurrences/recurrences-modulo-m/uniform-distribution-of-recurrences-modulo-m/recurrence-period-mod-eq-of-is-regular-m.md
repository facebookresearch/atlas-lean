# Regular recurrences with the same parameters share their periods

Let $a, b$ be integers and $w, w'$ integer sequences with $w_{n+2} = aw_{n+1} + bw_n$ and $w'_{n+2} = aw'_{n+1} + bw'_n$. If $p$ is a prime with $p \nmid b$ and both $w$ and $w'$ are $p$-regular, then for every $e \ge 1$, $\lambda_w(p^e) = \lambda_{w'}(p^e)$ and $h_w(p^e) = h_{w'}(p^e)$. Here $w$ is $p$-regular when $w_0 w_2 - w_1^2 \not\equiv 0 \pmod p$, $\lambda_w(m)$ is the least $\ell > 0$ with $w_{n+\ell} \equiv w_n \pmod m$ for all $n$ ($0$ if none), and $h_w(m)$ is the least $f > 0$ such that $w_{n+f} \equiv M w_n \pmod m$ for all $n$ for some integer $M$ coprime to $m$ ($0$ if none).

## Sources

- L. Somer and M. Křížek, Generalization of a theorem of Vélez on uniform distribution in second-order linear recurrences, Integers 25 (2025), Article A1, Lemma 2.2 (vii).
