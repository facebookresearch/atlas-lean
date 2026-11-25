# Stirling numbers from derivatives of powers of one minus the exponential

For all natural
numbers $k$, $r$ and $v$, write ${a \brace b}$ for the Stirling numbers of the second kind and
${a \brace b}_v$ for the r-Stirling numbers of the second kind with parameter $v$, and use the
convention $0^0 = 1$. Then the real functions $x \mapsto (1 - e^x)^k$ and
$x \mapsto (1 - e^x)^k e^{vx}$ satisfy

$$\frac{d^r}{dx^r} (1 - e^x)^k \Big|_{x=0} = \sum_{p=0}^{k} (-1)^p \binom{k}{p} p^r =
(-1)^k k! {r \brace k}$$

and

$$\frac{d^r}{dx^r} (1 - e^x)^k e^{vx} \Big|_{x=0} = \sum_{p=0}^{k} (-1)^p \binom{k}{p} (v+p)^r =
(-1)^k k! {r+v \brace k+v}_v.$$

## Sources

- Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109, Lemma 1.
