# Effective population size under fluctuating population size

In a neutral Wright–Fisher population of diploids whose size in generation $i$ is $N_i \ge 1$
($2N_i$ gene copies), the probability $h_t$ that two distinct gene copies of generation $t$ are not
identical by descent satisfies $h_{i+1} = (1 - 1/(2N_i))\,h_i$, because two distinct gene copies of
generation $i + 1$ are copies of the same gene of generation $i$ with probability $1/(2N_i)$ and otherwise
copies of two distinct genes of generation $i$. Hence

$$h_t = \Phi_t\, h_0, \qquad \Phi_t = \prod_{i=0}^{t-1} \Bigl(1 - \frac{1}{2N_i}\Bigr) .$$

The inbreeding effective size over these $t \ge 1$ generations, the constant size $N_e$ of a
Wright–Fisher population giving the same factor $\Phi_t$ (equal to $h_t / h_0$ when $h_0 > 0$), is

$$N_e = \frac{1}{2\Bigl(1 - \prod_{i<t} \bigl(1 - \tfrac{1}{2N_i}\bigr)^{1/t}\Bigr)} .$$

Let $N_H = t / \sum_{i<t} N_i^{-1}$ be the harmonic mean of the sizes. Then

$$0 \le t \log\Bigl(1 - \frac{1}{2N_H}\Bigr) - \sum_{i<t} \log\Bigl(1 - \frac{1}{2N_i}\Bigr) \le
\sum_{i<t} \frac{1}{4N_i^2} ,$$

so $\Phi_t$ equals $(1 - 1/(2N_H))^t$ up to a factor in $[e^{-E}, 1]$ with $E = \sum_{i<t} 1/(4N_i^2)$,
and $N_H$ is at most the geometric and the arithmetic mean of the $N_i$. The lower bound is concavity of
$x \mapsto \log(1 - x)$, as $1/(2N_H)$ is the mean of the $1/(2N_i)$; the upper bound uses
$0 \le -\log(1 - x) - x \le x^2$ for $0 \le x \le 1/2$.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 course text, University of Washington, version of December 2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section VI.7 "Varying population size and offspring number", equations (VI-39)–(VI-44),
  pp. 268–270 (the product formula, the exact effective number and the harmonic-mean approximation).
