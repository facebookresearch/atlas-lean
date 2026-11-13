# Rosser–Iwaniec linear sieve

Let $\gamma$ be the Euler–Mascheroni constant, $C_0$ a real
number, and $F, f \colon \mathbb{R} \to \mathbb{R}$ functions continuous on $(0, \infty)$ with
$F(s) = 2e^{\gamma}/s$ for $0 < s \le 3$ and $f(s) = 0$ for $0 < s \le 2$, such that
$u \mapsto uF(u)$ has derivative $f(s - 1)$ at every $s > 3$ and $u \mapsto uf(u)$ has derivative
$F(s - 1)$ at every $s > 2$. Then $f(s) = 2e^{\gamma}\log(s - 1)/s$ for $2 \le s \le 4$, and there
is a constant $C > 0$ with the following property. Let $P$ be a set of primes, $\omega$ a
non-negative multiplicative arithmetic function with $\omega(p) < p$ for $p \in P$, $A$ a finite
multiset of positive integers, and $X > 0$ and $2 \le z \le y$ real numbers such that
$\sum_{p \in P,\ t \le p < z} \omega(p) \log p / p \le \log(z/t) + C_0$ for every real $t$ with
$2 \le t \le z$. Write $P(z) = \prod_{p \in P,\ p < z} p$,
$V(z) = \prod_{p \in P,\ p < z} (1 - \omega(p)/p)$ and $s = \log y / \log z$; let $S$ be the number
of elements of $A$ coprime to $P(z)$ and $\#A_d$ the number of elements of $A$ divisible by $d$,
both counted with multiplicity; and let
$R = \sum_{d \mid P(z),\ d < y} |\#A_d - \omega(d) X / d|$. Then
$S \le X V(z) (F(s) + C e^{-s} (\log y)^{-1/3}) + R$ and
$X V(z) (f(s) - C e^{-s} (\log y)^{-1/3}) - R \le S$.

## Sources

- Angel Calzado, *A Bombieri-Vinogradov Result to Address the Parity Problem*, INTEGERS 26 (2026), Article A117, Lemma 5.
