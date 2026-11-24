# Eventual bound for $C(k)B(k)$ by an explicit logarithm

Let $p_\ell$ denote the $\ell$-th
prime ($p_1 = 2$), $\log$ the natural logarithm, $\gamma$ the Euler–Mascheroni constant and $c_1$
the Meissel–Mertens constant. For $j \in \{1, 2, 3\}$ and $k \in \mathbb{N}$ put
$L(k) = (k+1)(\log(k+1) + \log\log(k+1))$, $L^-(k) = (k+1)(\log(k+1) + \log\log(k+1) - 1)$ and

$$C(k) = \log L(k) \cdot \exp\Bigl(c_1 - \frac{1}{p_j} + \frac{5}{\log L^-(k)}\Bigr),
\qquad B(k) = \prod_{\substack{1 \le \ell \le k+1 \\ \ell \ne j}} \frac{p_\ell^2}{p_\ell^2 - 1}.$$

Then there is $K \in \mathbb{N}$ such that for every $k \ge K$,

$$C(k)\,B(k) < e^{\gamma} \log\bigl(L^-(k) \log 2.51 - \log p_j\bigr).$$

## Sources

- Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Proposition 1.
