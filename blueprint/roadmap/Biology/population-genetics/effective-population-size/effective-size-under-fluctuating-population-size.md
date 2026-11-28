# Effective population size under fluctuating population size

In a neutral Wright–Fisher population of diploids whose size in generation $i$ is $N_i \ge 1$
($2N_i$ gene copies), each gene copy of generation $i + 1$ is a copy of a gene copy of generation $i$
chosen uniformly at random, independently of the other gene copies. Two gene copies of generation $t$
are identical by descent if they descend from the same gene copy of generation $0$, or from two gene
copies of generation $0$ that are identical by descent, as a given relation on the gene copies of
generation $0$ records. Let $h_t$ be the probability that two distinct gene copies of generation $t$,
drawn at random, are not identical by descent. Then $h_{i+1} = (1 - 1/(2N_i))\,h_i$ for every $i$,
because two distinct gene copies of generation $i + 1$ are copies of the same gene of generation $i$
with probability $1/(2N_i)$ and otherwise copies of two distinct genes of generation $i$. Hence, for
every $t$,

$$h_t = \Phi_t\, h_0, \qquad \Phi_t = \prod_{i=0}^{t-1} \Bigl(1 - \frac{1}{2N_i}\Bigr) ,$$

so $\Phi_t = h_t / h_0$ when $h_0 > 0$.

Let $t \ge 1$. The inbreeding effective size over these $t$ generations,

$$N_e = \frac{1}{2\Bigl(1 - \Bigl(\prod_{i<t} \bigl(1 - \tfrac{1}{2N_i}\bigr)\Bigr)^{1/t}\Bigr)} ,$$

is greater than $1/2$, and it is the only $M > 1/2$ with $(1 - 1/(2M))^t = \Phi_t$: the constant size
of a Wright–Fisher population giving the same factor $\Phi_t$.

Let $N_H = t / \sum_{i<t} N_i^{-1}$ be the harmonic mean of the sizes and $E = \sum_{i<t} 1/(4N_i^2)$.
Then

$$0 \le t \log\Bigl(1 - \frac{1}{2N_H}\Bigr) - \sum_{i<t} \log\Bigl(1 - \frac{1}{2N_i}\Bigr) \le E ,$$

so $\Phi_t / (1 - 1/(2N_H))^t$ lies in $[e^{-E}, 1]$, and

$$N_H \le \Bigl(\prod_{i<t} N_i\Bigr)^{1/t} \le \frac{1}{t} \sum_{i<t} N_i ,$$

that is, the harmonic mean of the sizes is at most their geometric mean, which is at most their
arithmetic mean. The lower bound on the logarithms is concavity of $x \mapsto \log(1 - x)$, as
$1/(2N_H)$ is the mean of the $1/(2N_i)$; the upper bound uses $0 \le -\log(1 - x) - x \le x^2$ for
$0 \le x \le 1/2$.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 course text, University of Washington, version of December 2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section VI.7 "Varying population size and offspring number", equations (VI-39)–(VI-44),
  pp. 268–270 (the product formula, the exact effective number and the harmonic-mean approximation).
