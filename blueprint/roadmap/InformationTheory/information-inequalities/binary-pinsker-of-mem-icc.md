# Binary Pinsker inequality on the closed interval

Let $0 \le u \le 1$ and $0 < v < 1$. Then, with the natural logarithm and the convention
$0 \log 0 = 0$,

$$
2 (u - v)^2 \le u \log \frac{u}{v} + (1 - u) \log \frac{1 - u}{1 - v},
$$

that is, $2\,\mathrm{TV}(\mathrm{Ber}(u), \mathrm{Ber}(v))^2 \le D(\mathrm{Ber}(u) \,\|\, \mathrm{Ber}(v))$.
It is the case $0 < v < 1$ of the binary inequality behind the
[finite Pinsker inequality](csiszar-kullback-pinsker.md), which allows $u$ and $v$ anywhere in
$[0, 1]$ as long as $v = 0$ forces $u = 0$ and $v = 1$ forces $u = 1$; that inequality is proved
by convexity of an auxiliary function.

## Sources

- Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge University Press, 2025), Theorem 7.10 (proof: reduction of Pinsker's inequality to Bernoulli distributions).
