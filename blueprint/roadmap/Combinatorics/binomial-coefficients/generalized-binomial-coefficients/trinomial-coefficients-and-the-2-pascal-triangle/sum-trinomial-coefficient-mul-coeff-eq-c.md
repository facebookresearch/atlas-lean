# Sums of trinomial coefficients along lines by coefficient extraction

Write $[t^j]\,g$
for the coefficient of $t^j$ in a power series $g$, and $f_k = [t^k]\,f$. For $n \in \mathbb{N}$
let $\binom{n}{j}_2 = [t^j]\,(1+t+t^2)^n$ be the trinomial coefficient. For complex $u$ and $z$
let $(1 + zt + z^2t^2)^u$ be the binomial series $\sum_{i \ge 0} \binom{u}{i} (zt + z^2t^2)^i$,
and for complex $u$ let $\binom{u}{j}_2 = [t^j]\,(1+t+t^2)^u$. Let $n, x, a, b, m, c$ be natural
numbers with $2a < b$ and $c > 0$, let $y, z \in \mathbb{C}$, let $a'$ be an integer and let
$f \in \mathbb{C}[[t]]$. Then

$$\sum_{k=0}^{2n} \binom{n+ak}{x+bk}_2 z^{2(n+ak)-(x+bk)} f_k =
[t^{2n}]\, (1-zt+z^2t^2)^n \frac{t^x}{(1-zt)^{x+1}}\,
f\!\left(\frac{t^{b-2a} (1-zt+z^2t^2)^a}{(1-zt)^b}\right),$$

where a term with $x + bk > 2(n+ak)$ is $0$ because its trinomial coefficient is, and

$$\sum_{k=0}^{\lfloor m/c \rfloor} \binom{y+a'k}{m-ck}_2 z^{m-ck} f_k =
[t^m]\, (1+zt+z^2t^2)^y\, f\big(t^c (1+zt+z^2t^2)^{a'}\big).$$

The paper allows integers $x$ and $a$ in the first identity and obtains the second as the case
$b = -c < 0$; $\binom{u}{j}_2$ for complex $u$ is Comtet's extension (the paper's Eq. (8)).

## Sources

- Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of Integer Sequences 28 (2025), Article 25.3.5, Theorem 7 (`jis-2025-25.3.5-thm-7`).
